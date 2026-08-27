#!/usr/bin/env python3
"""Fail on any `shape_search --duplicates` group that is not on record.

`examples/shape_search.rs --duplicates` (ADR-0608) reports declarations that
share an admitted *type shape*.  As of 2026-08-27 it reports 10 such groups,
and a lane read every one by hand (not just the shape or the name):

    docs/research/11-design-review/2026-08-27-shape-search-duplicates-adjudicated.md

Six are deliberate zero-cost aliases (one proof term, two names), one is an
intentional cross-check (two independent proofs of one statement, kept on
purpose), and three were accidental independent re-derivations -- all three
now fixed to forward to a single proof term.  So today's true count is: ten
groups, ten adjudicated reasons, zero live hazards.

The risk this script exists to close: a NEW accidental duplicate lands the
same way the three fixed ones did -- a lane cannot find an existing lemma
(see CLAUDE.md's "THE LEMMA YOU NEED USUALLY EXISTS" entry) and proves it
again under a new name -- and nothing notices until the next time someone
runs `--duplicates` by hand. This script is that gate, run automatically:

  * A group `shape_search` reports that is NOT in
    `scripts/shape-duplicates-allowlist.json` (by exact name-set) is
    reported as a NEW/UNADJUDICATED duplicate and FAILS the gate. It must be
    read (statement + proof term, not just shape) and either fixed (alias
    one to the other) or -- only if it is genuinely deliberate, like the
    Apollonius cross-check -- added to the allowlist with a *reason*.

  * An allowlist entry whose name-set is NO LONGER reported by
    `shape_search` is STALE and also FAILS the gate. This is the
    `#[expect]`-style half of the check: an allowlist is only trustworthy if
    it is checked in both directions, or it silently accumulates entries for
    duplicates that were fixed, renamed, or removed without anyone updating
    the record -- and a stale "this is fine, see reason X" is worse than no
    record, because it reads as still-considered when it is not.

  * Every allowlist entry must carry a non-empty `reason`. An allowlist
    without reasons is how a gate becomes decoration (CLAUDE.md).

Usage::

    python3 scripts/check-shape-duplicates.py
    python3 scripts/check-shape-duplicates.py --duplicates-file captured.txt
    python3 scripts/check-shape-duplicates.py --allowlist my-allowlist.json

Exit 0: every reported group is allowlisted and every allowlist entry is
still reported. Exit 1: a new/unadjudicated duplicate or a stale allowlist
entry (or both) was found. Exit 2: the tool itself could not be run, or the
allowlist file is malformed -- not a finding about duplicates, a broken gate.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_ALLOWLIST = REPO_ROOT / "scripts" / "shape-duplicates-allowlist.json"

DUPLICATE_PREFIX = "DUPLICATE  "
VERDICT_RE = re.compile(r"^verdict: DUPLICATE-GROUPS (\d+)\s*$", re.MULTILINE)


class DuplicatesFormatError(ValueError):
    """`shape_search --duplicates` output does not have the expected shape."""


class AllowlistError(ValueError):
    """`scripts/shape-duplicates-allowlist.json` is malformed."""


def parse_duplicates(text: str) -> list[tuple[str, frozenset[str]]]:
    """Parse `shape_search --duplicates` stdout.

    Returns `(shape, names)` pairs in report order. `shape_search` joins its
    three columns with a literal double space (`DUPLICATE  <shape>
    <names...>`, with `<shape>` itself containing single-spaced `->` arrows
    and `<names...>` single-space-joined) -- splitting on a single space
    would shred the shape column, so this splits on the literal `"  "`
    separator the tool actually emits.
    """
    groups: list[tuple[str, frozenset[str]]] = []
    for line in text.splitlines():
        if not line.startswith(DUPLICATE_PREFIX):
            continue
        parts = line.split("  ")
        if len(parts) != 3:
            raise DuplicatesFormatError(
                f"malformed DUPLICATE line (expected 3 double-space-separated "
                f"fields, got {len(parts)}): {line!r}"
            )
        _, shape, names_field = parts
        names = tuple(n for n in names_field.split(" ") if n)
        if len(names) < 2:
            raise DuplicatesFormatError(
                f"DUPLICATE line names {names!r} fewer than 2 -- not a duplicate group: {line!r}"
            )
        groups.append((shape, frozenset(names)))
    return groups


def parse_verdict_count(text: str) -> int | None:
    """The tool's own `verdict: DUPLICATE-GROUPS N` line, if present."""
    m = VERDICT_RE.search(text)
    return int(m.group(1)) if m else None


def load_allowlist(path: Path) -> dict[frozenset[str], dict]:
    """Load and validate the allowlist. Raises `AllowlistError` on any defect."""
    try:
        raw = path.read_text()
    except OSError as exc:
        raise AllowlistError(f"cannot read {path}: {exc}") from exc
    try:
        data = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise AllowlistError(f"{path} is not valid JSON: {exc}") from exc
    if not isinstance(data, list):
        raise AllowlistError(f"{path}: top level must be a JSON list, got {type(data).__name__}")

    out: dict[frozenset[str], dict] = {}
    for i, entry in enumerate(data):
        if not isinstance(entry, dict):
            raise AllowlistError(f"{path}: entry {i} is not an object")
        names = entry.get("names")
        if not isinstance(names, list) or len(names) < 2 or not all(isinstance(n, str) for n in names):
            raise AllowlistError(
                f"{path}: entry {i} 'names' must be a JSON list of >= 2 strings, got {names!r}"
            )
        reason = entry.get("reason")
        if not isinstance(reason, str) or not reason.strip():
            raise AllowlistError(
                f"{path}: entry {i} ({names}) has no non-empty 'reason' -- "
                "an allowlist entry without a reason is how a gate becomes decoration"
            )
        key = frozenset(names)
        if len(key) != len(names):
            raise AllowlistError(f"{path}: entry {i} lists a name more than once: {names!r}")
        if key in out:
            raise AllowlistError(f"{path}: two entries name the same group {sorted(names)!r}")
        out[key] = entry
    return out


def run_shape_search(cargo_bin: str = "cargo") -> str:
    """Run the real tool. Raises `RuntimeError` if the tool itself failed."""
    cmd = [
        cargo_bin,
        "run",
        "--release",
        "-q",
        "-p",
        "axeyum-lean-kernel",
        "--example",
        "shape_search",
        "--",
        "--include-constructed",
        "--duplicates",
    ]
    proc = subprocess.run(
        cmd, cwd=REPO_ROOT, capture_output=True, text=True, timeout=900, check=False
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"`{' '.join(cmd)}` exited {proc.returncode} -- the tool itself failed, "
            f"this is not a finding about duplicates:\nSTDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}"
        )
    return proc.stdout


def evaluate(
    reported: list[tuple[str, frozenset[str]]], allowed: dict[frozenset[str], dict]
) -> tuple[list[tuple[str, frozenset[str]]], list[tuple[frozenset[str], dict]]]:
    """Return `(unrecognized, stale)`.

    `unrecognized`: reported groups whose name-set has no allowlist entry --
    a duplicate that has never been adjudicated (new, or an existing group
    whose membership changed, e.g. a third declaration joined a pair).

    `stale`: allowlist entries whose name-set is no longer reported -- the
    group stopped being a duplicate (fixed some other way, renamed, or one
    of the names was removed) and the allowlist was not updated to match.
    """
    reported_keys = {names for _, names in reported}
    unrecognized = [(shape, names) for shape, names in reported if names not in allowed]
    stale = [(names, entry) for names, entry in allowed.items() if names not in reported_keys]
    return unrecognized, stale


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--allowlist", type=Path, default=DEFAULT_ALLOWLIST)
    parser.add_argument(
        "--duplicates-file",
        type=Path,
        default=None,
        help="read shape_search --duplicates stdout from this file instead of "
        "invoking cargo (for testing against a captured or synthetic fixture)",
    )
    parser.add_argument("--cargo-bin", default="cargo")
    args = parser.parse_args(argv)

    try:
        allowed = load_allowlist(args.allowlist)
    except AllowlistError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 2

    if args.duplicates_file is not None:
        try:
            text = args.duplicates_file.read_text()
        except OSError as exc:
            print(f"FAIL: cannot read {args.duplicates_file}: {exc}", file=sys.stderr)
            return 2
    else:
        try:
            text = run_shape_search(args.cargo_bin)
        except RuntimeError as exc:
            print(f"FAIL: {exc}", file=sys.stderr)
            return 2

    try:
        reported = parse_duplicates(text)
    except DuplicatesFormatError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 2

    verdict_count = parse_verdict_count(text)
    if verdict_count is not None and verdict_count != len(reported):
        print(
            f"FAIL: shape_search's own verdict line says {verdict_count} duplicate "
            f"group(s) but this gate parsed {len(reported)} DUPLICATE line(s) -- "
            "output truncated (check for --limit) or parsing broke silently",
            file=sys.stderr,
        )
        return 2

    unrecognized, stale = evaluate(reported, allowed)
    ok = True

    if unrecognized:
        ok = False
        print(f"FAIL: {len(unrecognized)} duplicate group(s) not on the allowlist:", file=sys.stderr)
        for shape, names in unrecognized:
            print(f"  NEW/UNADJUDICATED  {shape}  {' '.join(sorted(names))}", file=sys.stderr)
        print(
            "  Read the actual statements and proof terms (not just the shape) before\n"
            "  deciding what this is. If it is an accidental independent re-derivation,\n"
            "  fix it (make one declaration a thin alias forwarding to the other's proof\n"
            "  term). If it is genuinely deliberate (like the Apollonius cross-check),\n"
            f"  add it to {args.allowlist} with a reason. See\n"
            "  docs/research/11-design-review/2026-08-27-shape-search-duplicates-adjudicated.md",
            file=sys.stderr,
        )

    if stale:
        ok = False
        plural = "y is" if len(stale) == 1 else "ies are"
        print(f"FAIL: {len(stale)} allowlist entr{plural} stale (no longer reported):", file=sys.stderr)
        for names, entry in stale:
            print(f"  STALE  {' '.join(sorted(names))}  (recorded reason: {entry['reason']!r})", file=sys.stderr)
        print(
            f"  Remove the entry from {args.allowlist}, or find out why shape_search\n"
            "  stopped reporting it -- a rename can hide behind this just as easily as\n"
            "  a genuine fix.",
            file=sys.stderr,
        )

    if ok:
        print(f"OK: {len(reported)} duplicate group(s), all allowlisted with a reason.")
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(main())
