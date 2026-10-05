#!/usr/bin/env python3
"""Move finished lane status files out of PLAN.md's inputs, keeping every link.

`PLAN.md` is generated from every file in `docs/plan/status/`. Nothing ever took
a finished lane back out, so by 2026-10-05 it rolled up 770 lanes -- 601 of them
DONE -- into 75,717 lines, and the "read first" tracker could not be read. This
moves a lane file into `docs/plan/archive/lanes/`, where it stays searchable
(`docs/plan/CATALOG.md` indexes it) but no longer feeds the plan.

A move must not break anything that pointed at the file, so for each lane it:

1. rebases the moved file's own relative links (resolved from the old
   directory, re-expressed from the new one; root-relative links are left as
   written because `check-links.sh` accepts them from either place);
2. rewrites every markdown link in the repository that resolved to the old
   path, and every plain-text `docs/plan/status/<lane>.md` mention in tracked
   text files (code comments, scripts, JSON), to the new path.

It never touches a file with uncommitted changes, and it refuses to overwrite
an existing archive entry.

Usage:
    scripts/archive-plan-lane.py LANE [LANE ...]        # names or paths
    scripts/archive-plan-lane.py --done                  # every DONE lane
    scripts/archive-plan-lane.py --all                   # every lane
    add --dry-run to print the plan without writing
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
STATUS = ROOT / "docs/plan/status"
DEST = ROOT / "docs/plan/archive/lanes"
LINK = re.compile(r"(?<=\]\()(?!https?://|mailto:|#|/)([^)\s]+)(?=\))")
TEXT_SUFFIXES = {".md", ".py", ".rs", ".sh", ".json", ".toml", ".yml", ".yaml", ".txt", ".tsv", ""}
# The lane-status block's own status token, e.g. **Your lane's block (`DONE`, lane, 2026-09-01).**
STATUS_TOKEN = re.compile(r"\(\s*`([A-Za-z][A-Za-z -]*)`\s*,")
DONE_WORDS = {"DONE", "LANDED", "COMPLETE", "CLOSED", "MERGED"}


def git(*args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=ROOT, capture_output=True, text=True, check=True
    ).stdout


def dirty() -> set[Path]:
    out = git("status", "--porcelain", "-z")
    paths = set()
    for entry in out.split("\0"):
        if len(entry) > 3:
            paths.add((ROOT / entry[3:]).resolve())
    return paths


def lane_status(path: Path) -> str | None:
    match = STATUS_TOKEN.search(path.read_text(encoding="utf-8")[:1200])
    return match.group(1).strip().upper() if match else None


def relink_own(body: str, old_dir: Path, new_dir: Path) -> str:
    def fix(match: re.Match[str]) -> str:
        target, sep, anchor = match.group(1).partition("#")
        if not target:
            return match.group(0)
        resolved = (old_dir / target).resolve()
        if not resolved.exists():
            return match.group(0)  # root-relative or already broken: leave it
        return os.path.relpath(resolved, new_dir) + sep + anchor

    return LINK.sub(fix, body)


def relink_inbound(path: Path, moves: dict[Path, Path]) -> str | None:
    try:
        body = path.read_text(encoding="utf-8")
    except (UnicodeDecodeError, OSError):
        return None
    original = body
    if "docs/plan/status/" not in body and "status/" not in body:
        return None
    here = path.parent
    if path.suffix == ".md":

        def fix(match: re.Match[str]) -> str:
            target, sep, anchor = match.group(1).partition("#")
            if not target:
                return match.group(0)
            for base in (here, ROOT):
                resolved = (base / target).resolve()
                if resolved in moves:
                    new = moves[resolved]
                    if base == ROOT:
                        return str(new.relative_to(ROOT)) + sep + anchor
                    return os.path.relpath(new, here) + sep + anchor
            return match.group(0)

        body = LINK.sub(fix, body)

    def plain(match: re.Match[str]) -> str:
        old = (ROOT / match.group(0)).resolve()
        return str(moves[old].relative_to(ROOT)) if old in moves else match.group(0)

    body = re.sub(r"docs/plan/status/[A-Za-z0-9._-]+?\.md", plain, body)
    return body if body != original else None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("lanes", nargs="*")
    parser.add_argument("--done", action="store_true", help="archive every DONE lane")
    parser.add_argument("--all", action="store_true", help="archive every lane")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument(
        "--include-dirty", action="store_true",
        help="also rewrite references in files with uncommitted changes "
        "(only in a worktree you own)",
    )
    args = parser.parse_args()

    candidates = sorted(p for p in STATUS.glob("*.md") if p.name != "README.md")
    if args.all:
        chosen = candidates
    elif args.done:
        chosen = [p for p in candidates if (lane_status(p) or "") in DONE_WORDS]
    else:
        chosen = []
        for name in args.lanes:
            stem = Path(name).name.removesuffix(".md")
            path = STATUS / f"{stem}.md"
            if not path.exists():
                print(f"archive-plan-lane: no such lane: {name}", file=sys.stderr)
                return 2
            chosen.append(path)
    if not chosen:
        print("archive-plan-lane: nothing to archive")
        return 0

    unclean = set() if args.include_dirty else dirty()
    moves: dict[Path, Path] = {}
    for path in chosen:
        if path.resolve() in unclean:
            print(f"archive-plan-lane: SKIP {path.relative_to(ROOT)} (uncommitted changes)")
            continue
        target = DEST / path.name
        if target.exists():
            print(f"archive-plan-lane: REFUSE {path.name}: {target.relative_to(ROOT)} exists", file=sys.stderr)
            return 1
        moves[path.resolve()] = target.resolve()
    print(f"archive-plan-lane: {len(moves)} lane(s) -> {DEST.relative_to(ROOT)}/")
    if args.dry_run:
        for old in moves:
            print(f"  {Path(old).relative_to(ROOT)}")
        return 0

    DEST.mkdir(parents=True, exist_ok=True)
    for old, new in moves.items():
        body = relink_own(old.read_text(encoding="utf-8"), old.parent, new.parent)
        new.write_text(body, encoding="utf-8")
        subprocess.run(["git", "add", "--", str(new)], cwd=ROOT, check=True)
        subprocess.run(["git", "rm", "-q", "--cached", "--", str(old)], cwd=ROOT, check=True)
        old.unlink()

    rewritten = 0
    for rel in git("ls-files", "-z").split("\0"):
        if not rel:
            continue
        path = ROOT / rel
        if path.suffix not in TEXT_SUFFIXES or not path.is_file() or path.resolve() in unclean:
            continue
        new_body = relink_inbound(path, moves)
        if new_body is not None:
            path.write_text(new_body, encoding="utf-8")
            rewritten += 1
    print(f"archive-plan-lane: rewrote references in {rewritten} file(s); "
          "regenerate with `python3 scripts/gen-plan.py`")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
