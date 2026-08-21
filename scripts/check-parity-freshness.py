#!/usr/bin/env python3
"""check-parity-freshness.py -- is the parity ledger's headline still current?

`bench-results/PARITY.md` is this repository's declared headline: an external
benchmark list pinned by sha256 BEFORE each run, the same machine, the same
24 s budget, and a `DISAGREEMENTS > 0` rule that voids an entry regardless of
its ratio.  It is written by `scripts/parity-run.sh`.

WHY THIS EXISTS
---------------
Measured 2026-08-21: `scripts/parity-run.sh` was invoked by **no gate** -- not
`just check`, not `scripts/check.sh`, not CI.  The consequence was not a wrong
number, it was a frozen one.  The last competition measurement of any logic
except QF_BV was 2026-08-06 -- fifteen days -- and that window covered the
steepest improvement in the project's history: UF went 32 -> 85 of 91 in four
days, QF_RDL 10 -> 105 in one.  The published board understated the project by
a wide margin and nothing went red, because a number that moves only when a
human chooses to move it does not move in a repository where humans move on.

So this is the piece `parity-run.sh` never had: something that FAILS when the
headline has gone stale.  It does not re-measure -- it is cheap, it reads a
committed markdown file -- it only makes the staleness impossible to not
notice.

WHAT COUNTS AS A MEASUREMENT (decided here, written down so the next lane does
not have to re-derive it)
-------------------------------------------------------------------------
  * The POPULATION is every logic that has ever appeared in the ledger.  It is
    derived from the append-only artifact, never from
    `bench-results/parity-lists/`, because a list can be deleted and the
    ledger cannot: anchoring to the ledger means a logic can never be dropped
    out of the tracked set to make this gate green.

  * An entry's AS-OF DATE is the timestamp in its own header, never the file's
    commit date.  `## <LOGIC> — <ISO8601Z>`, optionally followed by a further
    ` — <LABEL>` (today: ` — EVIDENCE MODE`).  A regex that forgets the
    optional label silently under-reports the freshest entry for that logic --
    that exact miss happened while the gap analysis was being written, and it
    would have made this gate report QF_BV as 19 days old instead of 4.  The
    header scan below therefore CLASSIFIES EVERY `## ` LINE and fails on one
    it does not recognise, so an unparsed entry can never read as an absent
    one (see MIN_LOGICS and the annotation allow-list).

  * EVIDENCE-MODE entries DO refresh the clock.  Their `certified / unsat`
    cell is not comparable to a default entry, but their scored counts come
    from the same default-route run at the same protocol budget --
    `parity-run.sh` adds the evidence run, it never substitutes it -- so the
    decide-rate this gate is about was genuinely re-measured.

  * A VOIDED entry does NOT refresh the clock.  The ledger's own rule is that
    `disagreements > 0` voids an entry regardless of its ratio; an entry that
    is not a valid measurement cannot be a recent one either.  The newest
    NON-voided entry per logic is the as-of date, and any voided entry in the
    ledger is reported separately because it is a soundness alarm, not a
    statistic.

  * A logic with a committed benchmark list and NO ledger entry is reported as
    `unmeasured`, and does not fail this gate.  That is a coverage gap, not a
    staleness one, and the two want different remedies; failing here would red
    the gate on a condition unrelated to what it protects, which is how gates
    get overridden reflexively.  The count is in the machine-readable line so
    it cannot hide.

THE THRESHOLD, AND WHY IT IS 14 DAYS
------------------------------------
Not a round number chosen because it looks tidy.  Two bounds, and 14 is where
they meet.

  * IT MUST FIRE ON ITS OWN MOTIVATING INCIDENT.  The stall this gate exists
    for was 2026-08-06 -> 2026-08-21: fifteen days.  Any budget of 15 days or
    more would have sat green through the entire episode, which is the "checker
    that cannot fail" shape CLAUDE.md counts 40 instances of.  14 is the
    largest budget that reds on it.

  * IT MUST BE AFFORDABLE, OR IT TRAINS PEOPLE TO IGNORE IT.  A division is
    200 benchmarks x 2 solvers x up to 24 s wall = 2.7 h worst case.  The real
    cost is readable out of the ledger itself: the four sequential entries one
    lane produced on 2026-08-06 (QF_NIA 08:46, QF_LIA 09:54, QF_LRA 12:44,
    QF_RDL 13:54) are 68, 170 and 70 minutes apart, so call it 1-3 h per
    division.  Nine divisions is most of a day on a machine four lanes share
    and that already serializes every heavy cargo job behind one flock,
    alongside the ~110-minute `local-ci.sh` battery on its own 48 h budget.
    At 14 days the steady-state obligation is nine divisions per fortnight --
    one sweep every ~1.6 days, a few percent of the box.  At 7 days it is
    double that and starts competing with the battery for the same lock.

  * THE BUDGET IS PER LOGIC, WHICH IS WHAT MAKES 14 AFFORDABLE.  This gate
    names the single stalest division and the one command that fixes it, so a
    red costs one sweep, not a board refresh.  A gate whose remedy costs a day
    of machine time gets overridden; a gate whose remedy costs ninety minutes
    gets satisfied.

  * WALL-CLOCK, NOT COMMITS.  Same reasoning as
    `scripts/check-local-ci-freshness.sh`: velocity here is bursty (171
    commits in one 24 h window, quiet weekends), so a commit-count ceiling is
    either red-by-construction during a burst or blind during a lull.  And
    what actually decays is the correspondence between a PUBLISHED number and
    reality, which is a calendar exposure by nature.

A WARNING BAND at 10 days prints the obligation four days before it is
enforced, so a lane can batch a sweep into machine time it was already using
rather than being ambushed by a red on the day it wanted to land something.
The warning never changes the exit status.

FRESHNESS IS NOT CORRECTNESS, AND THIS GATE MEASURES ONLY THE FIRST
------------------------------------------------------------------
A date says when a number was produced, not whether the tree that produced it
still resembles HEAD.  The failure this permits is worse than the one the gate
prevents, and it nearly happened on the day the gate landed: a QF_UFLIA sweep
was in flight from a tree that did not contain `40a1ab969` (ADR-0538), a
one-file change to `crates/axeyum-solver/src/dpll_lia.rs` worth +22 files on
that division.  An entry stamped with today's date carrying the pre-fix number
would have been **fresher-looking and more wrong** than the two-week-old entry
it replaced, and this gate would have gone green over it -- the gate's own front
door used to defeat the gate.

So every row also reports the currency of the tree it was measured on, read out
of the entry's `solver commit` field, which `scripts/parity-run.sh` has always
recorded:

  * whether that sha is resolvable in this checkout at all,
  * whether it is an ancestor of HEAD, and
  * `behind=N`, the number of commits touching `crates/` between it and HEAD.

All three are ADVISORY and none changes the exit status.  That is deliberate,
not timidity, and the reasoning is the same one that fixes the 14-day budget:

  * a commit-count bound is exactly the trap the threshold section rejects --
    velocity here is bursty (171 commits in one 24 h window, quiet weekends), so
    any fixed `behind=` ceiling is red-by-construction during a burst;
  * NON-ANCESTRY IS LEGITIMATE in this repository.  Lanes measure from their own
    branches and worktrees, so an entry another lane appended can carry a sha
    that is simply not on your line of history.  Failing on it would red your
    aggregate gate for something you cannot fix, which is how gates get
    overridden reflexively;
  * a sha can vanish from a shared checkout (a rewritten or unmerged branch);
    two 2026-08-02 entries in this very ledger already have.

What the numbers ARE for: they put "was fix X in this measurement?" one
`git merge-base --is-ancestor <solver-commit> <fix>` away, mechanically, instead
of leaving it to whoever happens to remember.  When `behind=` is large on a
division somebody just improved, re-measure that division -- do not reason about
whether it matters.

WHAT TO DO WHEN THIS REDS.  Almost always: run the sweep it names.

    cargo build --release -p axeyum-bench --example smtcomp_cli
    scripts/parity-run.sh <LOGIC>          # ~1-3 h, appends to the ledger
    # then commit bench-results/PARITY.md and bench-results/parity-details/

Do NOT narrow a denominator, re-time an old entry, or edit the ledger: it is
append-only precisely so a number that goes down stays visible.  If the sweep
comes out worse than the last entry, that entry still gets appended.

Usage:
  scripts/check-parity-freshness.py                       # enforcing
  scripts/check-parity-freshness.py --ledger P --lists D  # point at a fixture
  scripts/check-parity-freshness.py --now 2026-08-21T00:00:00Z

Env:
  AXEYUM_PARITY_FRESHNESS_MAX_AGE_DAYS   fail budget in days (default 14)
  AXEYUM_PARITY_FRESHNESS_WARN_AGE_DAYS  warn budget in days (default 10)

Exit: 0 fresh (warnings allowed) / 1 at least one logic stale / 2 the ledger
could not be read as a ledger (unrecognised header, malformed entry, or a
suspiciously small population -- a broken parser must not read as a green
board).
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_LEDGER = ROOT / "bench-results" / "PARITY.md"
DEFAULT_LISTS = ROOT / "bench-results" / "parity-lists"

# A measurement entry.  The trailing ` — <LABEL>` group is what makes
# `— EVIDENCE MODE` parse; without it the freshest QF_BV entry is invisible.
ENTRY_RE = re.compile(
    r"^## (?P<logic>[A-Z][A-Z0-9_]*)"
    r" — (?P<ts>\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z)"
    r"(?: — (?P<label>.+))?$"
)

# Prose the ledger legitimately carries between entries.  Anything that is
# neither an entry nor one of these is a header shape nobody anticipated, and
# it exits 2 rather than being skipped -- silently skipping is how a parser
# under-reports without anyone noticing.
ANNOTATION_RE = re.compile(r"^## (?:Correction|Note|Addendum|Retraction) — ")

DISAGREEMENTS_RE = re.compile(
    r"^\| \*\*disagreements\*\* \| \*\*(?P<value>\d+)\*\* \|$", re.MULTILINE
)
RATIO_RE = re.compile(
    r"^\| \*\*ratio \(axeyum / reference\)\*\* \| \*\*(?P<value>[^|]+)\*\* \|$",
    re.MULTILINE,
)
SOLVED_RE = re.compile(r"^\| axeyum solved \| (?P<value>[^|]+) \|$", re.MULTILINE)
# `scripts/parity-run.sh` writes this on every entry. It may carry a trailing
# " (DIRTY WORKTREE — result not reproducible)" stamp, so match only the sha.
SOLVER_COMMIT_RE = re.compile(
    r"^\| solver commit \| `(?P<value>[0-9a-f]{7,40})`", re.MULTILINE
)
REFERENCE_SOLVED_RE = re.compile(
    r"^\| reference solved \| (?P<value>[^|]+) \|$", re.MULTILINE
)

# A population this small means the parser is looking at the wrong thing.  The
# ledger has carried nine or more logics since 2026-08-06; an empty or
# near-empty read is a broken glob or a moved file, and a gate that passes
# vacuously on it is worse than no gate.
MIN_LOGICS = 5


def solver_currency(sha: str, repo: Path) -> tuple[str, int | None]:
    """Classify an entry's `solver commit` against this checkout.

    Returns (state, behind) where state is one of "ok" (resolvable ancestor of
    HEAD), "non-ancestor", "unresolvable", or "no-git", and `behind` counts the
    commits touching `crates/` between that sha and HEAD when computable.

    Every branch is ADVISORY -- see this script's header for why none of them
    may fail the gate. Returns "no-git" rather than raising when git is absent
    or the path is not a checkout, because a fixture-driven control points this
    script at a throwaway directory and a currency probe must never be the
    reason a staleness gate cannot run.
    """
    if not sha:
        return ("unresolvable", None)

    def git(*args: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            ["git", "-C", str(repo), *args],
            capture_output=True,
            text=True,
            check=False,
        )

    if git("rev-parse", "--git-dir").returncode != 0:
        return ("no-git", None)
    if git("cat-file", "-e", f"{sha}^{{commit}}").returncode != 0:
        return ("unresolvable", None)
    if git("merge-base", "--is-ancestor", sha, "HEAD").returncode != 0:
        return ("non-ancestor", None)
    counted = git("rev-list", "--count", f"{sha}..HEAD", "--", "crates")
    behind = None
    if counted.returncode == 0 and counted.stdout.strip().isdigit():
        behind = int(counted.stdout.strip())
    return ("ok", behind)


class LedgerError(Exception):
    """The ledger could not be read as a ledger."""


def parse_ledger(text: str, source: str) -> list[dict]:
    """Return one record per measurement entry, in file order.

    Raises LedgerError on any `## ` header that is neither a recognised entry
    nor a recognised annotation, and on any entry missing the rows this gate
    reads.
    """
    lines = text.splitlines()
    starts: list[tuple[int, re.Match]] = []
    for i, line in enumerate(lines):
        if not line.startswith("## "):
            continue
        m = ENTRY_RE.match(line)
        if m:
            starts.append((i, m))
            continue
        if ANNOTATION_RE.match(line):
            continue
        raise LedgerError(
            f"{source}:{i + 1}: unrecognised '## ' header {line!r}.\n"
            "  A header this parser does not classify would be SKIPPED, and a\n"
            "  skipped entry is indistinguishable from a missing one -- which\n"
            "  is exactly how a stale logic reads as fresh. If this is a new\n"
            "  entry shape, teach ENTRY_RE about it; if it is prose, add its\n"
            "  keyword to ANNOTATION_RE. Do not widen either to a catch-all."
        )

    records: list[dict] = []
    for idx, (line_no, m) in enumerate(starts):
        end = starts[idx + 1][0] if idx + 1 < len(starts) else len(lines)
        body = "\n".join(lines[line_no + 1 : end])
        dis = DISAGREEMENTS_RE.search(body)
        if dis is None:
            raise LedgerError(
                f"{source}:{line_no + 1}: entry {m.group('logic')} "
                f"{m.group('ts')} has no '**disagreements**' row. Every entry\n"
                "  written by scripts/parity-run.sh has one; without it this\n"
                "  gate cannot tell a valid measurement from a voided one."
            )
        ratio = RATIO_RE.search(body)
        solved = SOLVED_RE.search(body)
        ref_solved = REFERENCE_SOLVED_RE.search(body)
        records.append(
            {
                "logic": m.group("logic"),
                "ts": datetime.strptime(m.group("ts"), "%Y-%m-%dT%H:%M:%SZ").replace(
                    tzinfo=timezone.utc
                ),
                "label": m.group("label") or "",
                "disagreements": int(dis.group("value")),
                "solver_commit": (
                    SOLVER_COMMIT_RE.search(body).group("value")
                    if SOLVER_COMMIT_RE.search(body)
                    else ""
                ),
                "ratio": (ratio.group("value").strip(" `*") if ratio else "?"),
                "solved": (solved.group("value").strip(" `*") if solved else "?"),
                "reference_solved": (
                    ref_solved.group("value").strip(" `*") if ref_solved else "?"
                ),
                "line": line_no + 1,
            }
        )
    return records


def main() -> int:
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("--ledger", default=str(DEFAULT_LEDGER))
    ap.add_argument("--lists", default=str(DEFAULT_LISTS))
    ap.add_argument(
        "--now",
        default=None,
        help="evaluate as of this instant (ISO8601 Z); default: real time. "
        "Exists so the control suite is deterministic.",
    )
    ap.add_argument(
        "--repo",
        default=str(ROOT),
        help="checkout whose HEAD the `solver commit` currency is read against; "
        "advisory only, and degrades to 'no-git' when this is not a checkout.",
    )
    ap.add_argument("--max-age-days", type=float, default=None)
    ap.add_argument("--warn-age-days", type=float, default=None)
    args = ap.parse_args()

    max_days = (
        args.max_age_days
        if args.max_age_days is not None
        else float(os.environ.get("AXEYUM_PARITY_FRESHNESS_MAX_AGE_DAYS", "14"))
    )
    warn_days = (
        args.warn_age_days
        if args.warn_age_days is not None
        else float(os.environ.get("AXEYUM_PARITY_FRESHNESS_WARN_AGE_DAYS", "10"))
    )

    if args.now:
        now = datetime.strptime(args.now, "%Y-%m-%dT%H:%M:%SZ").replace(
            tzinfo=timezone.utc
        )
    else:
        now = datetime.now(timezone.utc)

    ledger = Path(args.ledger)
    if not ledger.is_file():
        print(
            f"PARITY_FRESHNESS_ERROR|no ledger at {ledger}; the headline this "
            "gate guards does not exist",
            file=sys.stderr,
        )
        return 2

    try:
        records = parse_ledger(ledger.read_text(encoding="utf-8"), str(ledger))
    except LedgerError as exc:
        print(f"PARITY_FRESHNESS_ERROR|{exc}", file=sys.stderr)
        return 2

    logics = sorted({r["logic"] for r in records})
    if len(logics) < MIN_LOGICS:
        print(
            f"PARITY_FRESHNESS_ERROR|parsed only {len(logics)} logic(s) from "
            f"{ledger} ({len(records)} entries). The ledger has carried nine or "
            "more since 2026-08-06, so this is a broken parser or the wrong "
            "file, and a near-empty population would make this gate pass "
            "vacuously.",
            file=sys.stderr,
        )
        return 2

    voided = [r for r in records if r["disagreements"] > 0]

    # Newest NON-voided entry per logic.
    asof: dict[str, dict] = {}
    for r in records:
        if r["disagreements"] > 0:
            continue
        cur = asof.get(r["logic"])
        if cur is None or r["ts"] > cur["ts"]:
            asof[r["logic"]] = r

    # Logics that appear ONLY as voided entries have no valid measurement at
    # all.  Treat that as infinitely stale, not as absent.
    never_valid = [lg for lg in logics if lg not in asof]

    lists_dir = Path(args.lists)
    listed = sorted(p.stem for p in lists_dir.glob("*.txt")) if lists_dir.is_dir() else []
    unmeasured = [lg for lg in listed if lg not in {r["logic"] for r in records}]

    rows = []
    for lg in logics:
        r = asof.get(lg)
        if r is None:
            rows.append((lg, None, None, "NEVER-VALID"))
            continue
        age = (now - r["ts"]).total_seconds() / 86400.0
        state = "ok"
        if age > max_days:
            state = "STALE"
        elif age > warn_days:
            state = "warn"
        rows.append((lg, r, age, state))
    rows.sort(key=lambda t: (-1e9 if t[2] is None else -t[2]))

    stale = [t for t in rows if t[3] in ("STALE", "NEVER-VALID")]
    warned = [t for t in rows if t[3] == "warn"]

    currency: dict[str, tuple[str, int | None]] = {}
    for lg, r in asof.items():
        currency[lg] = solver_currency(r["solver_commit"], Path(args.repo))
    lags = [b for (_st, b) in currency.values() if b is not None]
    max_lag = max(lags) if lags else 0
    unresolvable = sum(1 for (st, _b) in currency.values() if st == "unresolvable")
    non_ancestor = sum(1 for (st, _b) in currency.values() if st == "non-ancestor")

    print(f"parity ledger freshness — {ledger} as of {now:%Y-%m-%dT%H:%M:%SZ}")
    print(f"  budget: warn > {warn_days:g}d, FAIL > {max_days:g}d (per logic)")
    print(
        f"  {'logic':<10} {'age(d)':>7}  {'measured':<20} {'ratio':>7}  "
        "state  [solver commit / currency — ADVISORY]"
    )
    for lg, r, age, state in rows:
        if r is None:
            print(f"  {lg:<10} {'--':>7}  {'(no valid entry)':<20} {'--':>7}  {state}")
            continue
        label = "evidence" if "EVIDENCE" in r["label"] else ""
        cur_state, behind = currency.get(lg, ("no-git", None))
        if cur_state == "ok":
            cur = f"{r['solver_commit'][:9]} behind={behind}"
        else:
            cur = f"{r['solver_commit'][:9] or '?'} {cur_state.upper()}"
        print(
            f"  {lg:<10} {age:>7.1f}  {r['ts']:%Y-%m-%dT%H:%MZ}  "
            f"{r['ratio']:>7}  {state}{(' [' + label + ']') if label else ''}"
            f"  [{cur}]"
        )

    stalest_name = rows[0][0] if rows else "-"
    stalest_days = "inf" if (rows and rows[0][2] is None) else (
        f"{rows[0][2]:.1f}" if rows else "0"
    )

    if unmeasured:
        print(
            f"  note: committed benchmark list(s) never measured: "
            f"{','.join(unmeasured)} (coverage gap, not staleness — reported, "
            "not enforced; see this script's header)"
        )
    for r in voided:
        print(
            f"  VOIDED ENTRY (does not refresh the clock): {r['logic']} "
            f"{r['ts']:%Y-%m-%dT%H:%MZ} at {ledger}:{r['line']} — "
            f"{r['disagreements']} disagreement(s)",
            file=sys.stderr,
        )

    print(
        "PARITY_FRESHNESS"
        f"|logics={len(logics)}"
        f"|stalest={stalest_name}"
        f"|stalest_days={stalest_days}"
        f"|max_days={max_days:g}"
        f"|warn_days={warn_days:g}"
        f"|stale={len(stale)}"
        f"|warn={len(warned)}"
        f"|voided={len(voided)}"
        f"|unmeasured={len(unmeasured)}"
        f"|max_solver_lag={max_lag}"
        f"|unresolvable_solver_commit={unresolvable}"
        f"|non_ancestor_solver_commit={non_ancestor}"
        f"|verdict={'FAIL' if stale else 'PASS'}"
    )

    if stale:
        print("", file=sys.stderr)
        for lg, r, age, state in stale:
            when = "never (only voided entries)" if r is None else f"{age:.1f} days ago"
            print(
                f"PARITY_FRESHNESS_ERROR|{lg} was last validly measured {when}, "
                f"past the {max_days:g}-day budget",
                file=sys.stderr,
            )
        print("", file=sys.stderr)
        print(
            "  The remedy is to re-measure, one division at a time, stalest "
            "first:",
            file=sys.stderr,
        )
        print(
            "    cargo build --release -p axeyum-bench --example smtcomp_cli",
            file=sys.stderr,
        )
        for lg, _r, _age, _state in stale[:3]:
            print(f"    scripts/parity-run.sh {lg}", file=sys.stderr)
        print(
            "  Do NOT edit the ledger, re-time an entry, or narrow a "
            "denominator. It is append-only so a number that goes down stays "
            "visible; a worse result still gets appended.",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
