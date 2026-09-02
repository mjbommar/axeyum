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

TWO ROUTES TO THE SAME ANSWER, AND WHY THE SECOND ONE EXISTS.

Until 2026-09-02 there was one route: `cargo run --release ... shape_search`.
That is correct, and it is why this gate lived only in `scripts/check.sh` /
`just check` / CI -- the ~10-minute gate CLAUDE.md itself says is not run per
merge. Measured by lane `retrieval-audit-0901`: this gate was **red on main
for about 25 hours** and appears in **0 of the 240 commit messages** of that
day, and a literal duplicate declaration landed 16 hours after its twin
inside that window. The check worked; nobody ran it.

So `--prebuilt` runs `target/release/examples/shape_search` DIRECTLY -- no
cargo, no `cargo-serialized.sh` flock, no build -- which is cheap enough for
`scripts/check-merge-hygiene.sh` (ADR-1511: cheap checks block a merge,
expensive ones get a no-cargo proxy there). Same pattern as
`scripts/gen-py-prelude-fields.py --check` and `scripts/fact-frontier.py`.

**A STALE PREBUILT BINARY MUST NEVER ANSWER.** It indexes the declarations it
was compiled against, so it reports duplicate groups for an OLD environment:
a duplicate that landed after the build is invisible (a false PASS on exactly
the question this gate exists to answer), and an allowlist entry for a group
that has since been fixed reads as STALE (a false FAIL). The staleness test is
`fact-frontier.py`'s `kernel_projection_is_stale`, imported rather than
re-implemented -- one definition of "newer than any kernel source", one place
to fix it.

Usage::

    python3 scripts/check-shape-duplicates.py              # cargo, the full gate
    python3 scripts/check-shape-duplicates.py --prebuilt   # no cargo, merge gate
    python3 scripts/check-shape-duplicates.py --duplicates-file captured.txt
    python3 scripts/check-shape-duplicates.py --allowlist my-allowlist.json

Exit 0: every reported group is allowlisted and every allowlist entry is
still reported. Exit 1: a new/unadjudicated duplicate or a stale allowlist
entry (or both) was found. Exit 2: the question could not be answered -- not
a finding about duplicates, a broken gate.

**EXIT 2 ALONE IS NOT ENOUGH TO DECIDE WHETHER A CALLER MAY SKIP**, and a
caller that treats every 2 as "skipped" turns a real defect into silence. Two
different things exit 2: a MALFORMED ALLOWLIST (a defect in a committed file,
which must block a merge) and an ABSENT-OR-STALE PREBUILT BINARY (a fact about
this host's `target/`, which must not). Only the second prints, as its first
line on stdout::

    SHAPE-DUPLICATES|UNAVAILABLE <reason-token> -- <one-line explanation>

with `<reason-token>` one of `no-binary`, `stale-binary`, `tool-failed`.
`check-merge-hygiene.sh` keys on that marker, not on the exit code alone.
"""

from __future__ import annotations

import argparse
import importlib.util
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


PREBUILT_BIN = REPO_ROOT / "target" / "release" / "examples" / "shape_search"
FACT_FRONTIER = REPO_ROOT / "scripts" / "fact-frontier.py"

UNAVAILABLE_MARKER = "SHAPE-DUPLICATES|UNAVAILABLE"


class PrebuiltUnavailable(Exception):
    """The prebuilt binary cannot answer: absent, stale, or it failed.

    Carries a `token` (`no-binary` / `stale-binary` / `tool-failed`) so a
    caller can report WHICH unanswerable state this is without parsing prose.
    """

    def __init__(self, token: str, detail: str) -> None:
        super().__init__(detail)
        self.token = token
        self.detail = detail


def _relative(path: Path) -> str:
    """`path` as written in this repository, when it is inside it."""
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def _staleness_test():
    """`fact-frontier.py`'s `kernel_projection_is_stale`, imported not copied.

    "Is this binary older than any kernel source" is a single fact about the
    tree, and two copies of it drift the moment one learns about a directory
    the other does not.

    The file's name has a hyphen so it is not importable as a module; it is
    import-safe (module level is constants plus an `if __name__` guard), so
    `spec_from_file_location` is enough. Raises `PrebuiltUnavailable` rather
    than crashing if it cannot be loaded -- "cannot tell" degrades to
    no-answer, never to a confident pass.
    """
    try:
        spec = importlib.util.spec_from_file_location(
            "_axeyum_fact_frontier_for_shape_duplicates", FACT_FRONTIER
        )
        if spec is None or spec.loader is None:
            raise ImportError(f"no import spec for {FACT_FRONTIER}")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        return module.kernel_projection_is_stale
    except (OSError, ImportError, AttributeError, SyntaxError) as exc:
        raise PrebuiltUnavailable(
            "tool-failed",
            f"cannot import kernel_projection_is_stale from {_relative(FACT_FRONTIER)}: {exc}",
        ) from exc


def run_shape_search_prebuilt(binary: Path = PREBUILT_BIN, timeout: float = 900.0) -> str:
    """Run the already-built `shape_search` directly. No cargo, no lock.

    Raises `PrebuiltUnavailable` when the binary is absent, older than a
    kernel source, or exits nonzero. Every one of those is "I cannot answer",
    never "there are no duplicates" -- see the module docstring.
    """
    if not binary.exists():
        raise PrebuiltUnavailable(
            "no-binary",
            f"{_relative(binary)} has never been built here; run"
            " `scripts/cargo-serialized.sh build --release -p axeyum-lean-kernel"
            " --example shape_search`",
        )
    is_stale = _staleness_test()
    if is_stale(binary):
        raise PrebuiltUnavailable(
            "stale-binary",
            f"{_relative(binary)} is older than a file under"
            " crates/axeyum-lean-kernel/src, so it indexes an OLD environment;"
            " rebuild it before believing any verdict from it",
        )
    cmd = [str(binary), "--include-constructed", "--duplicates"]
    try:
        proc = subprocess.run(
            cmd, cwd=REPO_ROOT, capture_output=True, text=True, timeout=timeout, check=False
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise PrebuiltUnavailable("tool-failed", f"`{' '.join(cmd)}` did not run: {exc}") from exc
    if proc.returncode != 0:
        tail = (proc.stderr or proc.stdout).strip().splitlines()
        raise PrebuiltUnavailable(
            "tool-failed",
            f"`{' '.join(cmd)}` exited {proc.returncode}: {tail[-1] if tail else 'no output'}",
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
    parser.add_argument(
        "--prebuilt",
        action="store_true",
        help="run target/release/examples/shape_search directly instead of "
        "invoking cargo -- no build, no cargo-serialized.sh flock, cheap "
        "enough for scripts/check-merge-hygiene.sh (ADR-1511). Exits 2 with a "
        f"leading `{UNAVAILABLE_MARKER} <token>` line when the binary is absent "
        "or older than a kernel source, rather than answering from a stale index.",
    )
    parser.add_argument(
        "--prebuilt-bin",
        type=Path,
        default=PREBUILT_BIN,
        help="override the prebuilt binary path (controls only)",
    )
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
    elif args.prebuilt:
        try:
            text = run_shape_search_prebuilt(args.prebuilt_bin)
        except PrebuiltUnavailable as exc:
            # The marker goes to STDOUT and comes FIRST, because the caller
            # that needs it (check-merge-hygiene.sh) has to tell this apart
            # from the other exit-2 cause, a malformed allowlist, which is a
            # real defect and must block. See the module docstring.
            print(f"{UNAVAILABLE_MARKER} {exc.token} -- {exc.detail}")
            print(
                f"FAIL: cannot answer from the prebuilt binary ({exc.token}): {exc.detail}",
                file=sys.stderr,
            )
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
        route = "prebuilt" if args.prebuilt else ("file" if args.duplicates_file else "cargo")
        print(
            f"OK: {len(reported)} duplicate group(s), all allowlisted with a reason. "
            f"(route: {route})"
        )
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(main())
