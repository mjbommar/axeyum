#!/usr/bin/env python3
"""Generate the ADR index from the ADR files themselves.

``docs/research/09-decisions/README.md`` used to be hand-appended: every ADR
added a row, and the file was touched 60 times in 24 hours by concurrent lanes.
Two of those appends were silently overwritten on 2026-08-14.  An index is a
*view*, so it is derived here instead of maintained.

Sources, all per-ADR so that two lanes writing two ADRs never edit one file:

* ``README-preamble.md`` — the hand-authored purpose/process/template prose,
  emitted verbatim ahead of the generated table.
* every ``adr-NNNN-*.md`` — its ``# ADR-NNNN: Title`` heading plus the
  ``Key: value`` front-matter block that follows it.

Front matter keys this reads:

``Status``
    Required.  The ADR's own status line.
``Index-summary``
    Optional.  The index row's title cell when the ADR's own heading is not the
    text the index should carry.  363 of the 454 rows carried a curated summary
    that existed *only* in the hand-maintained index; migrating them into the
    ADRs is what makes this generator lossless.
``Index-status``
    Optional.  The index row's status cell when the ADR's ``Status`` line is
    qualified ("accepted (equality slice implemented …)") but the index cell is
    the bare verdict.

Regenerate with ``python3 scripts/gen-adr-index.py``; ``--check`` fails when the
committed file differs from a fresh generation, which is what makes a hand edit
a gate failure rather than a lost line.

``--check-remote`` is a second, independent mode: it does not touch the index
at all, and instead compares this checkout's ADR *numbers* against
``--remote-ref``'s tree (default ``origin/main``) to catch two checkouts
minting the same number for two different decisions -- a defect ``--check``
structurally cannot see, because it only ever reads the working tree.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
DECISIONS = ROOT / "docs" / "research" / "09-decisions"
PREAMBLE = DECISIONS / "README-preamble.md"
OUTPUT = DECISIONS / "README.md"

DEFAULT_REMOTE_REF = "origin/main"
DEFAULT_MAX_STALENESS_HOURS = 24.0

HEADING = re.compile(r"^# ADR-(\d{4}):[ \t]*(.+?)[ \t]*$")
NUMBERED_FILENAME = re.compile(r"^adr-(\d{4})-")
# Three front-matter styles are in the tree and all nine of the bullet-list
# ones were invisible to a naive '^Status:' scan: "Status: accepted",
# "- Status: proposed", and "- **Status:** accepted".
FRONT_MATTER = re.compile(
    r"^(?:-[ \t]+)?(?:\*\*)?([A-Za-z][A-Za-z0-9-]*)(?:\*\*)?:(?:\*\*)?[ \t]*(.*?)[ \t]*$"
)

BANNER = (
    "> **Generated; do not edit by hand.** Every row is derived from the "
    "`adr-*.md` file it links to (its heading, `Status:`, and optional "
    "`Index-summary:` / `Index-status:` front matter) plus the hand-authored "
    "[`README-preamble.md`](README-preamble.md). Regenerate with "
    "`python3 scripts/gen-adr-index.py`; `--check` is a gate. Editing this file "
    "directly is how index rows got silently overwritten twice on 2026-08-14."
)


class AdrError(Exception):
    """A malformed ADR file: reported, never silently skipped."""


def display(path: Path) -> str:
    """Repo-relative when possible; `relative_to` raises on anything else."""
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def parse_adr(path: Path) -> dict[str, str]:
    """Read one ADR's number, heading title, and front-matter block."""
    lines = path.read_text(encoding="utf-8").splitlines()
    heading = HEADING.match(lines[0]) if lines else None
    if heading is None:
        raise AdrError(f"{path.name}: first line is not '# ADR-NNNN: Title'")
    number, title = heading.group(1), heading.group(2)

    front: dict[str, str] = {}
    index = 1
    while index < len(lines) and not lines[index].strip():
        index += 1
    # The front matter is the run of `Key: value` lines that starts the file.
    # The first line that is not one -- a blank line, or the prose continuation
    # ADR-0059 puts between its `Index-status:` and `Date:` -- ends it.
    #
    # This stop is load-bearing, not tidiness: ADR bodies quote the template
    # ("Status: proposed | accepted | ...") and several discuss `Index-summary`
    # by name, so a whole-file scan reads prose as metadata and rewrites the
    # row from a sentence that was only ever an example.
    while index < len(lines):
        field = FRONT_MATTER.match(lines[index])
        if field is None:
            break
        front[field.group(1)] = field.group(2)
        index += 1

    if "Status" not in front:
        raise AdrError(f"{path.name}: no 'Status:' line in its front matter")

    row_title = front.get("Index-summary") or title
    row_status = front.get("Index-status") or front["Status"]
    for label, cell in (("title", row_title), ("status", row_status)):
        if "|" in cell:
            raise AdrError(
                f"{path.name}: {label} contains '|', which would break the table row"
            )

    return {
        "number": number,
        "path": path.name,
        "title": row_title,
        "status": row_status,
        "curated": "yes" if "Index-summary" in front else "no",
    }


def row_sort_key(adr: dict[str, str]) -> tuple[str, str]:
    """Total order over rows.

    ADR numbers are *not* unique — `0166` and `0167` name two ADRs each — so
    sorting on the number alone leaves those rows in whatever order the
    filesystem handed them over, which is not reproducible.  The filename is
    the tiebreak.
    """
    return (adr["number"], adr["path"])


def collect() -> list[dict[str, str]]:
    adrs = [parse_adr(path) for path in DECISIONS.glob("adr-*.md")]
    if not adrs:
        raise AdrError(f"no adr-*.md files under {DECISIONS}")
    adrs.sort(key=row_sort_key)
    return adrs


def render(preamble: str, adrs: list[dict[str, str]]) -> str:
    if "## Index" in preamble:
        raise AdrError(
            f"{PREAMBLE.name} contains its own '## Index' heading; the index is generated"
        )
    body = preamble.rstrip("\n").splitlines()
    if not body or not body[0].startswith("# "):
        raise AdrError(f"{PREAMBLE.name} must start with a level-1 heading")

    out = [body[0], "", BANNER, *body[1:], "", "## Index", "", "| ADR | Title | Status |", "|---|---|---|"]
    out.extend(
        f"| [{adr['number']}]({adr['path']}) | {adr['title']} | {adr['status']} |"
        for adr in adrs
    )
    return "\n".join(out) + "\n"


# --- Cross-checkout number collisions -------------------------------------
#
# `--check` above (and the `duplicate_numbers` field it prints) only ever
# looks at THIS working tree. ADR numbers are a shared append point across
# checkouts exactly like PLAN.md and this file's own generated index were
# before they were split per-lane — except a sequential number has no
# per-lane path to split it into. Two lanes in two checkouts each read "the
# highest number I can see" and can get the same answer without either one
# doing anything wrong. `--check-remote` below is the detector for that: it
# never edits a number, it only refuses to let two DIFFERENT ADRs land under
# one number without the collision being named out loud.


def _run_git(args: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True)


def remote_ref_commit(ref: str) -> str | None:
    """The commit `ref` resolves to in this checkout, or None if it does not.

    `None` covers every reason a ref can fail to resolve here: `origin` is not
    configured, `ref` was never fetched, or the checkout has no `.git` at all.
    Callers must treat all of those as "cannot check", not as "no collision".
    """
    result = _run_git(["rev-parse", "--verify", "--quiet", ref])
    return result.stdout.strip() or None if result.returncode == 0 else None


def remote_adr_filenames(ref: str) -> list[str]:
    """Basenames of every `adr-NNNN-*.md` in `ref`'s tree at this path.

    Call only after `remote_ref_commit(ref)` is not None — this raises
    `AdrError` on failure rather than returning `None`, because by the time
    this runs the ref was already confirmed to resolve, so a failure here is
    a different, worse problem (e.g. the path does not exist at that ref).
    """
    relative = str(DECISIONS.relative_to(ROOT))
    result = _run_git(["ls-tree", "-r", "--name-only", ref, "--", relative])
    if result.returncode != 0:
        raise AdrError(
            f"'git ls-tree {ref} -- {relative}' failed: {result.stderr.strip()}"
        )
    return [
        Path(line).name
        for line in result.stdout.splitlines()
        if NUMBERED_FILENAME.match(Path(line).name)
    ]


def fetch_head_age_seconds() -> float | None:
    """Seconds since the last `git fetch` in this checkout.

    `None` means "never fetched" (no `FETCH_HEAD`), which `check_remote`
    treats as maximally stale rather than crashing on it.
    """
    result = _run_git(["rev-parse", "--git-path", "FETCH_HEAD"])
    if result.returncode != 0:
        return None
    fetch_head = ROOT / result.stdout.strip()
    if not fetch_head.is_file():
        return None
    return max(0.0, time.time() - fetch_head.stat().st_mtime)


def _numbered(filenames: list[str]) -> dict[str, set[str]]:
    """Filenames grouped by their 4-digit ADR number; non-matching names skip."""
    grouped: dict[str, set[str]] = {}
    for name in filenames:
        match = NUMBERED_FILENAME.match(name)
        if match is None:
            continue
        grouped.setdefault(match.group(1), set()).add(name)
    return grouped


def find_remote_collisions(
    local_filenames: list[str], remote_filenames: list[str]
) -> list[tuple[str, list[str], list[str]]]:
    """Numbers claimed, for DIFFERENT files, by both `local` and `remote`.

    A number present on both sides under the SAME filename is shared history,
    not a collision. A collision is a number where each side has a file the
    OTHER side has never seen — two lanes independently minted it.
    """
    local_by_number = _numbered(local_filenames)
    remote_by_number = _numbered(remote_filenames)
    collisions: list[tuple[str, list[str], list[str]]] = []
    for number in sorted(set(local_by_number) & set(remote_by_number)):
        local_only = sorted(local_by_number[number] - remote_by_number[number])
        remote_only = sorted(remote_by_number[number] - local_by_number[number])
        if local_only and remote_only:
            collisions.append((number, local_only, remote_only))
    return collisions


def next_free_number(local_filenames: list[str], remote_filenames: list[str]) -> str:
    """One past the highest numbered ADR filename on either side."""
    numbers = [
        int(match.group(1))
        for filenames in (local_filenames, remote_filenames)
        for name in filenames
        for match in (NUMBERED_FILENAME.match(name),)
        if match is not None
    ]
    if not numbers:
        raise AdrError("no numbered adr-NNNN-*.md files found on either side")
    return f"{max(numbers) + 1:04d}"


def check_remote(remote_ref: str, max_staleness_hours: float, require_fresh: bool) -> int:
    """Compare this checkout's ADR numbers against `remote_ref`'s tree.

    Deliberate trade-offs, both spelled out here because CLAUDE.md's own
    account of this defect warns that either extreme silently defeats the
    gate:

    * An unresolvable `remote_ref` (no fetch ever ran, `origin` missing, no
      `.git` at all) does NOT fail this gate. Failing closed on that would
      make every offline lane red for a reason no amount of correct code
      fixes, which is exactly how a gate gets routed around rather than
      obeyed. It prints a loud SKIP instead and reports it in the summary
      line, so "this run did not actually check" is visible without being
      fatal.
    * A STALE `remote_ref` (older than `max_staleness_hours`, measured from
      `.git/FETCH_HEAD`'s mtime) is handled differently depending on what it
      found. A CLEAN result on stale data is downgraded to ADVISORY and still
      exits 0 by default — the data cannot rule out a collision landed on
      `remote_ref` since the last fetch, so a clean verdict from it would be
      confidently wrong in exactly the way that lets this defect survive.
      `--require-fresh` is the opt-in for a context that wants the harder
      guarantee (a fetch happens or the gate fails) instead of the default
      forgiving one. A COLLISION found on stale data is NOT downgraded by
      either mode: the two conflicting files existed as of the last fetch and
      neither can un-happen, so this still exits 1.
    """
    commit = remote_ref_commit(remote_ref)
    if commit is None:
        print(
            f"adr-collision: SKIP: '{remote_ref}' does not resolve in this "
            "checkout (no fetch has run, 'origin' is not configured, or this "
            f"is not a git checkout at all). This run did NOT check for "
            f"ADR-number collisions against {remote_ref}. Run "
            "`git fetch origin main` and re-run for real protection.",
            file=sys.stderr,
        )
        print(f"ADR_REMOTE_COLLISION|status=skipped_no_ref|remote_ref={remote_ref}")
        return 0

    local_filenames = sorted(path.name for path in DECISIONS.glob("adr-*.md"))
    try:
        remote_filenames = remote_adr_filenames(remote_ref)
    except AdrError as error:
        print(f"adr-collision: ERROR: {error}", file=sys.stderr)
        return 1

    collisions = find_remote_collisions(local_filenames, remote_filenames)
    next_free = next_free_number(local_filenames, remote_filenames)
    age = fetch_head_age_seconds()
    stale = age is None or age > max_staleness_hours * 3600.0
    age_field = "unknown" if age is None else f"{age:.0f}"

    if collisions:
        for number, local_only, remote_only in collisions:
            print(
                f"adr-collision: ERROR: ADR-{number} is claimed by both this "
                f"checkout and {remote_ref} for DIFFERENT decisions:",
                file=sys.stderr,
            )
            print(f"  local:         {', '.join(local_only)}", file=sys.stderr)
            print(f"  {remote_ref}: {', '.join(remote_only)}", file=sys.stderr)
        print(
            f"adr-collision: next free ADR number is {next_free} (highest used "
            f"across local + {remote_ref} at commit {commit[:12]}"
            f"{', STALE fetch data' if stale else ''})",
            file=sys.stderr,
        )
        print(
            "ADR_REMOTE_COLLISION|"
            f"status=collision|collisions={len(collisions)}|next_free={next_free}|"
            f"remote_ref={remote_ref}|remote_commit={commit[:12]}|"
            f"fetch_head_age_s={age_field}|stale={'yes' if stale else 'no'}"
        )
        return 1

    if stale:
        age_desc = "of unknown age (no FETCH_HEAD)" if age is None else f"{age / 3600:.1f}h old"
        print(
            f"adr-collision: ADVISORY ONLY, NOT COMPARABLE: the {remote_ref} "
            f"remote-tracking ref is {age_desc} (threshold {max_staleness_hours:g}h). "
            f"A collision landed on {remote_ref} more recently than that would NOT "
            "be visible to this run — this is a clean result on OLD data, not a "
            "clean result. Run `git fetch origin main` before trusting it.",
            file=sys.stderr,
        )
        print(
            "ADR_REMOTE_COLLISION|"
            f"status=stale_clean|collisions=0|next_free={next_free}|"
            f"remote_ref={remote_ref}|remote_commit={commit[:12]}|"
            f"fetch_head_age_s={age_field}|stale=yes"
        )
        return 1 if require_fresh else 0

    print(
        "ADR_REMOTE_COLLISION|"
        f"status=clean|collisions=0|next_free={next_free}|"
        f"remote_ref={remote_ref}|remote_commit={commit[:12]}|"
        f"fetch_head_age_s={age_field}|stale=no"
    )
    return 0


# Numbers duplicated before this check existed, on both sides of every branch.
# Not licence for a third: `--check` fails on any duplicate outside this set,
# and fails again if one of these is repaired without being removed here.
GRANDFATHERED_DUPLICATES = {"0166", "0167"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail when the committed index differs from a fresh generation",
    )
    parser.add_argument(
        "--check-remote",
        action="store_true",
        help=(
            "compare ADR numbers against --remote-ref's tree instead of "
            "generating/checking the index; exits 1 on a real number collision"
        ),
    )
    parser.add_argument(
        "--remote-ref",
        default=DEFAULT_REMOTE_REF,
        help=f"remote-tracking ref to compare against (default: {DEFAULT_REMOTE_REF})",
    )
    parser.add_argument(
        "--max-staleness-hours",
        type=float,
        default=DEFAULT_MAX_STALENESS_HOURS,
        help=(
            "age of .git/FETCH_HEAD, in hours, past which a clean --check-remote "
            f"result is downgraded to advisory (default: {DEFAULT_MAX_STALENESS_HOURS:g})"
        ),
    )
    parser.add_argument(
        "--require-fresh",
        action="store_true",
        help="with --check-remote, fail (not warn) when the remote ref is stale",
    )
    args = parser.parse_args()

    if args.check_remote:
        return check_remote(args.remote_ref, args.max_staleness_hours, args.require_fresh)

    try:
        adrs = collect()
        rendered = render(PREAMBLE.read_text(encoding="utf-8"), adrs)
    except (AdrError, FileNotFoundError) as error:
        print(f"adr-index: ERROR: {error}", file=sys.stderr)
        return 1

    if args.check:
        current = OUTPUT.read_text(encoding="utf-8") if OUTPUT.is_file() else None
        if current != rendered:
            print(
                f"adr-index: ERROR: {display(OUTPUT)} is not what "
                "scripts/gen-adr-index.py produces. It is generated: put the change "
                "in the ADR file (or README-preamble.md) and rerun the generator.",
                file=sys.stderr,
            )
            return 1
    else:
        OUTPUT.write_text(rendered, encoding="utf-8")

    duplicates = sorted(
        number
        for number, count in Counter(adr["number"] for adr in adrs).items()
        if count > 1
    )
    print(
        "ADR_INDEX|"
        f"rows={len(adrs)}|"
        f"curated_summaries={sum(adr['curated'] == 'yes' for adr in adrs)}|"
        f"duplicate_numbers={','.join(duplicates) if duplicates else 'none'}"
    )

    # A DUPLICATE NUMBER NOW FAILS `--check`. Until 2026-08-19 it did not: the
    # field above was printed and the exit status was 0 regardless, so
    # `duplicate_numbers=0166,0167,0455` and `duplicate_numbers=none` were
    # indistinguishable to any gate. Demonstrated by planting a second
    # `adr-0455-*` file: `--check` printed the duplicate and exited 0.
    #
    # That is why a collision created after a merge went unnoticed until someone
    # read the output by eye. `--check-remote` is the pre-merge detector and it
    # is structurally blind here: it flags a number only when EACH side has a
    # file the other lacks, and after a merge the local tree holds both, so
    # local-only is non-empty and remote-only is empty. The two checks are not
    # redundant and neither subsumes the other.
    #
    # `0166` and `0167` are grandfathered because they predate this check on
    # both sides of every branch; they are not licence for a third. The set is a
    # RATCHET in both directions -- fixing one must also fail, so the allowlist
    # can only shrink deliberately rather than drifting.
    unexpected = sorted(set(duplicates) - GRANDFATHERED_DUPLICATES)
    repaired = sorted(GRANDFATHERED_DUPLICATES - set(duplicates))
    if unexpected:
        print(
            "ADR_INDEX_ERROR|duplicate ADR number(s) "
            f"{','.join(unexpected)}: two decisions claim the same number. "
            "ADR numbers are a shared append point across checkouts -- three "
            "collisions happened in one day on 2026-08-18/19 -- so renumber the "
            "one that has NOT been published on the shared trunk, and check "
            "`git ls-tree -r --name-only origin/main docs/research/09-decisions/` "
            "for a free number rather than taking the local maximum",
            file=sys.stderr,
        )
        return 1
    if repaired:
        print(
            "ADR_INDEX_ERROR|grandfathered duplicate(s) "
            f"{','.join(repaired)} are no longer duplicated. That is a repair: "
            "remove them from GRANDFATHERED_DUPLICATES so the allowlist shrinks "
            "with the defect instead of outliving it",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
