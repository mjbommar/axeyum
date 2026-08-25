#!/usr/bin/env python3
"""Resolve a conflict between two lanes that both ADDED items to one Rust file.

WHY THIS EXISTS. Two lanes adding functions at the same insertion point produce
a conflict that looks purely additive -- no line is changed by both -- so the
obvious resolution is "keep both sides". Measured 2026-08-25 merging two lanes
into `nat_prelude/finite_set.rs`: keeping both sides produced a file that does
not parse, three `mismatched closing delimiter` errors, because git's hunk
boundaries cut MID-ITEM. Each side's block ended with a dangling

    pub(super) fn declare_something(

whose parameter list was the *shared context after the hunk* -- that boilerplate
is byte-identical on both sides, so the differ aligned on it. `-X patience` did
not fix the alignment either.

THE CHEAP TELL is delimiter balance. A hunk side whose braces balance ended at
an item boundary and can be concatenated; a side with a nonzero balance cut an
item in half, and no ordering of the two sides can put it back together --
because the single shared tail belongs to exactly one of the two dangling
signatures.

    `check`  reports the balance per side and REFUSES when any side is cut.
    `splice` does the reconstruction instead: take our version of the file
             (which parses), take the merge base, and lift every top-level item
             that THEIR version has and neither of the other two do, by brace
             matching inside their own file where it is complete.

`splice` is deliberately narrow. It refuses on a name collision, refuses when
the anchor is absent, and reports what it moved so the result is checkable. It
does not resolve a genuine content conflict and must not be used for one: if
both sides EDITED the same item, this tool will say the item is not new and
leave it to you.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

CONFLICT_START = "<<<<<<< "
CONFLICT_MID = "======="
CONFLICT_END = ">>>>>>> "

PAIRS = {"{": "}", "(": ")", "[": "]"}

# A top-level Rust item this tool knows how to lift whole. Deliberately just
# functions: they are what lanes add to these prelude modules, and an item whose
# extent this tool cannot compute exactly is an item it must not move.
ITEM_RE = re.compile(r"^(?:pub\(super\) |pub\(crate\) |pub |)fn ([A-Za-z_][A-Za-z0-9_]*)", re.M)


LINE_COMMENT_RE = re.compile(r"//.*$", re.M)


def delimiter_balance(text: str) -> dict[str, int]:
    """Net opener-minus-closer count per pair, over CODE only.

    Line comments are stripped first, and that is not a nicety -- this
    repository's doc comments are full of interval notation like `[0,n)` and
    rustdoc links like [`Self::foo`], which are deliberately unbalanced as
    delimiters. Measured 2026-08-25: without stripping, a genuinely SAFE hunk
    reported `{'(': -2, '[': 2}` and the tool refused a merge that would have
    concatenated fine. That is the fail-closed direction, but a checker that
    cries wolf gets ignored, and being ignored is how it stops being a checker.

    Block comments and string literals are NOT handled. A block whose braces
    balance only because a `{` sits inside a string is still unsafe to
    concatenate, so counting it is the conservative reading; and `//` covers
    every comment in the prelude modules this tool is for.
    """
    out = {k: 0 for k in PAIRS}
    for ch in LINE_COMMENT_RE.sub("", text):
        for opener, closer in PAIRS.items():
            if ch == opener:
                out[opener] += 1
            elif ch == closer:
                out[opener] -= 1
    return out


def parse_hunks(text: str) -> list[dict]:
    hunks: list[dict] = []
    cur: dict | None = None
    side: str | None = None
    for lineno, line in enumerate(text.split("\n"), start=1):
        if line.startswith(CONFLICT_START):
            cur = {"line": lineno, "ours": [], "theirs": []}
            side = "ours"
            continue
        if cur is not None and side == "ours" and line.rstrip() == CONFLICT_MID:
            side = "theirs"
            continue
        if cur is not None and line.startswith(CONFLICT_END):
            hunks.append(cur)
            cur, side = None, None
            continue
        if cur is not None and side is not None:
            cur[side].append(line)
    if cur is not None:
        raise SystemExit("LANE_MERGE_ERROR|unterminated conflict hunk; the file is not a merge result")
    return hunks


def cmd_check(path: Path) -> int:
    text = path.read_text(encoding="utf-8")
    hunks = parse_hunks(text)
    if not hunks:
        print(f"LANE_MERGE|{path}|hunks=0|verdict=no-conflict")
        return 0
    cut = []
    for index, hunk in enumerate(hunks, start=1):
        for side in ("ours", "theirs"):
            bal = delimiter_balance("\n".join(hunk[side]))
            bad = {k: v for k, v in bal.items() if v != 0}
            state = "balanced" if not bad else f"CUT {bad}"
            print(f"  hunk {index} @L{hunk['line']:<6} {side:<7} {len(hunk[side]):>4} lines  {state}")
            if bad:
                cut.append((index, side, bad))
    if cut:
        print(
            f"LANE_MERGE|{path}|hunks={len(hunks)}|cut_sides={len(cut)}|"
            "verdict=BOTH-SIDES-UNSAFE"
        )
        print(
            "  At least one hunk side ends mid-item, so its trailing context is shared with the\n"
            "  other side's dangling item. Concatenating the sides in EITHER order produces a file\n"
            "  that does not parse. Use `splice`, or resolve by hand against each branch's own file."
        )
        return 1
    print(f"LANE_MERGE|{path}|hunks={len(hunks)}|cut_sides=0|verdict=both-sides-safe")
    return 0


def git_show(ref: str, path: str) -> str:
    return subprocess.run(
        ["git", "show", f"{ref}:{path}"], capture_output=True, text=True, check=True
    ).stdout


def items(source: str) -> dict[str, str]:
    """Map item name -> its full text, including the doc/comment block above it."""
    out: dict[str, str] = {}
    for match in ITEM_RE.finditer(source):
        start = source.rfind("\n\n", 0, match.start())
        start = 0 if start < 0 else start + 2
        try:
            open_brace = source.index("{", match.end())
        except ValueError:
            continue
        depth, cursor = 0, open_brace
        while cursor < len(source):
            if source[cursor] == "{":
                depth += 1
            elif source[cursor] == "}":
                depth -= 1
                if depth == 0:
                    break
            cursor += 1
        else:
            continue
        out[match.group(1)] = source[start : cursor + 1]
    return out


def cmd_splice(path: str, ours_ref: str, theirs_ref: str, base_ref: str | None, anchor: str) -> int:
    if base_ref is None:
        base_ref = subprocess.run(
            ["git", "merge-base", ours_ref, theirs_ref],
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
    ours_src = git_show(ours_ref, path)
    theirs_src = git_show(theirs_ref, path)
    base_src = git_show(base_ref, path)
    ours, theirs, base = items(ours_src), items(theirs_src), items(base_src)

    new = [n for n in theirs if n not in base and n not in ours]
    collide = [n for n in theirs if n not in base and n in ours]
    if collide:
        print(
            f"LANE_MERGE_ERROR|{path}: {len(collide)} item(s) added by BOTH sides: "
            f"{sorted(collide)}. That is a content conflict, not an additive one, and this "
            "tool must not guess which body to keep."
        )
        return 1
    if not new:
        print(
            f"LANE_MERGE_ERROR|{path}: their branch adds no item this branch lacks. Either the "
            "merge is not additive or the refs are wrong; splicing nothing would silently drop "
            "whatever the real conflict is."
        )
        return 1
    if anchor not in ours_src:
        print(f"LANE_MERGE_ERROR|{path}: anchor {anchor!r} is not in our version of the file")
        return 1

    block = "\n".join(theirs[n] for n in new) + "\n\n"
    at = ours_src.index(anchor)
    merged = ours_src[:at] + block + ours_src[at:]
    Path(path).write_text(merged, encoding="utf-8")
    bal = delimiter_balance(merged)
    bad = {k: v for k, v in bal.items() if v != 0}
    if bad:
        print(f"LANE_MERGE_ERROR|{path}: spliced result is unbalanced {bad}; not trusting it")
        return 1
    print(f"LANE_MERGE|{path}|spliced={len(new)}|items={new}|balance=ok")
    print(
        "  NOTE: item bodies were moved, NOT their call sites. Wire each new `declare_*` into its\n"
        "  dispatcher yourself, and remember DECLARATION ORDER is not visible to `cargo check`."
    )
    return 0


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("check", help="report whether keeping both sides is safe")
    c.add_argument("path", type=Path)
    s = sub.add_parser("splice", help="reconstruct from each branch's own file")
    s.add_argument("path")
    s.add_argument("--ours", default="HEAD")
    s.add_argument("--theirs", required=True)
    s.add_argument("--base", default=None)
    s.add_argument("--anchor", required=True, help="text in OUR file to insert the new items before")
    args = ap.parse_args(argv)
    if args.cmd == "check":
        return cmd_check(args.path)
    return cmd_splice(args.path, args.ours, args.theirs, args.base, args.anchor)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
