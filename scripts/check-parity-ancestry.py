#!/usr/bin/env python3
"""check-parity-ancestry.py -- does the newest board row measure the newest code?

`bench-results/PARITY.md` is append-only, and every entry
`scripts/parity-run.sh` writes records the `solver commit` it measured.  What
nothing checked, until this script, is whether those commits are ORDERED.

WHY THIS EXISTS
---------------
Measured 2026-09-08.  The ledger carried, on the same day and twenty-two lines
apart, a QF_UFLIA row reading `129/200` at `f24c61f91` and (in a lane's own
tree) a `151/200` at `26d9d80e3`.  `f24c61f91` is **not an ancestor of**
`26d9d80e3`.  Two rows, one division, one day -- and nothing in either row said
which tree it described *relative to the other*.  A reader taking the newest
timestamp got the smaller number and no signal at all that it came from a tree
missing the fix.

`scripts/check-parity-freshness.py` cannot catch this and says so in its own
header: it compares each row's timestamp to the clock and each row's commit to
**HEAD**, both advisory.  Neither comparison is between two ROWS.  Once both
lanes' branches merge, both shas become ancestors of HEAD and the
freshness gate reports `ok behind=N` for each -- perfectly green over a board
whose headline number is the older measurement.

So the question this script asks is the one the freshness gate structurally
cannot:

    for each division, is the NEWEST row's tree a descendant of the tree of
    every EARLIER row for that division?

If it is not, then some earlier row was measured on code the newest row does
not contain, and the newest row is not a statement about the current state of
that division.  The remedy is always the same and always available: re-measure
that division from a commit that descends from both.

WHAT IS COMPARED, AND WHAT IS NOT
---------------------------------
  * SERIES.  Rows are grouped by `(logic, reference)`, where `reference` is the
    ` — SECOND REFERENCE (<name>)` label when present and the empty string
    otherwise.  A yices2-referenced QF_LRA row and a cvc5-referenced one are
    two different measurements of two different things; ordering the second
    against the first would manufacture a finding out of a comparison nobody
    made.  `— EVIDENCE MODE` rows stay in the DEFAULT series on purpose: their
    scored counts come from the same default-route run at the same protocol
    budget (`parity-run.sh` adds the evidence run, it never substitutes it), so
    they are measurements of the same number.

  * VOIDED ROWS ARE EXCLUDED.  The ledger's own rule is that
    `disagreements > 0` voids an entry regardless of its ratio, and the
    freshness gate already refuses to let one refresh the clock.  A row that is
    not a valid measurement cannot be a code-ordering datum either.

  * UNRESOLVABLE SHAS ARE ADVISORY.  A sha can vanish from a checkout (a
    rewritten or unmerged branch); two 2026-08-02 entries in this very ledger
    already have.  There is no re-measurement that fixes an entry whose tree no
    longer exists, so failing on it would red the gate forever on a condition
    with no remedy -- the shape that trains people to override gates.  They are
    counted and named, never enforced.  Same for a checkout with no git at all
    (`no-git`), which is how a fixture-driven control points this script at a
    throwaway directory.

  * THE ROW ORDER USED IS FILE ORDER, NOT TIMESTAMP ORDER, and the two can
    disagree: `parity-run.sh` appends when a sweep FINISHES, so a long sweep
    started first can land after a short one started later.  File order is what
    "append-only" actually guarantees, and the newest row is defined here as
    the LAST one in the file for its series.  A timestamp that runs backwards
    against file order is reported (`OUT-OF-ORDER-TIMESTAMP`) because it means
    the two rows overlapped in time, which is worth knowing when reading a
    load-sensitive number -- but it is not what this gate fails on.

WHAT IT FAILS ON (exit 1)
-------------------------
For each series, every earlier valid row is compared against the newest valid
row of that series:

  * `NOT-ANCESTOR` -- the earlier row's commit is neither the newest row's
    commit nor an ancestor of it.  Two sub-cases, both reported by name because
    the reader's next move differs:

      - `SUPERSEDED-BY-OLDER-CODE`: the NEWEST row's commit is an ancestor of
        the earlier one.  The board's current number for that division was
        measured on strictly older code than a number already recorded.  This
        is the 129-after-151 shape.

      - `DIVERGENT`: neither is an ancestor of the other.  The two rows were
        measured on side branches, so no ordering between them exists at all
        and the pair cannot be read as a before/after.

A series whose newest row descends from every earlier row is `ok`, and a series
with one valid row is `ok` vacuously (nothing to order it against) -- that case
is in the control suite so the accepting path is not assumed.

WHAT TO DO WHEN THIS REDS
-------------------------
Re-measure the division it names, from a commit that descends from both trees
(in practice: current `origin/main`), and append:

    cargo build --release -p axeyum-bench --example smtcomp_cli
    scripts/parity-run.sh <LOGIC>

Do NOT edit or remove the older row.  The ledger is append-only precisely so a
number that went down stays visible; the fix is another row, never a deletion.

Usage:
  scripts/check-parity-ancestry.py                        # enforcing
  scripts/check-parity-ancestry.py --ledger P --repo R    # point at a fixture

Exit: 0 every series ordered (advisory findings allowed) / 1 at least one
series whose newest row is not a descendant of an earlier row / 2 the ledger
could not be read as a ledger.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_LEDGER = ROOT / "bench-results" / "PARITY.md"

# Same entry shape `check-parity-freshness.py` parses, and for the same reason:
# forgetting the optional trailing label makes the freshest entry for a logic
# invisible, which here would silently drop the row the gate is about.
ENTRY_RE = re.compile(
    r"^## (?P<logic>[A-Z][A-Z0-9_]*)"
    r" — (?P<ts>\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z)"
    r"(?: — (?P<label>.+))?$"
)
ANNOTATION_RE = re.compile(r"^## (?:Correction|Note|Addendum|Retraction) — ")
SECOND_REF_RE = re.compile(r"SECOND REFERENCE \((?P<name>[^)]+)\)")

DISAGREEMENTS_RE = re.compile(
    r"^\| \*\*disagreements\*\* \| \*\*(?P<value>\d+)\*\* \|$", re.MULTILINE
)
SOLVER_COMMIT_RE = re.compile(
    r"^\| solver commit \| `(?P<value>[0-9a-f]{7,40})`", re.MULTILINE
)
SOLVED_RE = re.compile(r"^\| axeyum solved \| (?P<value>[^|]+) \|$", re.MULTILINE)

# Same reasoning as the freshness gate's MIN_LOGICS: a near-empty read is a
# broken parser or the wrong file, and a gate that passes vacuously on it is
# worse than no gate.
MIN_LOGICS = 5


class LedgerError(Exception):
    """The ledger could not be read as a ledger."""


def parse_ledger(text: str, source: str) -> list[dict]:
    """One record per measurement entry, in FILE order.

    Raises LedgerError on any `## ` header that is neither a recognised entry
    nor a recognised annotation: a header this parser does not classify would
    be skipped, and a skipped row is indistinguishable from an absent one.
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
            f"{source}:{i + 1}: unrecognised '## ' header {line!r}. A header "
            "this parser does not classify would be SKIPPED, and a skipped row "
            "is indistinguishable from an absent one."
        )

    records: list[dict] = []
    for idx, (line_no, m) in enumerate(starts):
        end = starts[idx + 1][0] if idx + 1 < len(starts) else len(lines)
        body = "\n".join(lines[line_no + 1 : end])
        dis = DISAGREEMENTS_RE.search(body)
        if dis is None:
            raise LedgerError(
                f"{source}:{line_no + 1}: entry {m.group('logic')} "
                f"{m.group('ts')} has no '**disagreements**' row; without it "
                "this gate cannot tell a valid measurement from a voided one."
            )
        label = m.group("label") or ""
        second = SECOND_REF_RE.search(label)
        sha_m = SOLVER_COMMIT_RE.search(body)
        solved_m = SOLVED_RE.search(body)
        records.append(
            {
                "logic": m.group("logic"),
                "ts": datetime.strptime(m.group("ts"), "%Y-%m-%dT%H:%M:%SZ").replace(
                    tzinfo=timezone.utc
                ),
                "label": label,
                "reference": second.group("name") if second else "",
                "disagreements": int(dis.group("value")),
                "solver_commit": sha_m.group("value") if sha_m else "",
                "solved": solved_m.group("value").strip(" `*") if solved_m else "?",
                "line": line_no + 1,
            }
        )
    return records


class Git:
    """Ancestry primitives over one checkout, with a resolvability cache."""

    def __init__(self, repo: Path) -> None:
        self.repo = repo
        self._resolved: dict[str, bool] = {}
        self.available = self._run("rev-parse", "--git-dir").returncode == 0

    def _run(self, *args: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            ["git", "-C", str(self.repo), *args],
            capture_output=True,
            text=True,
            check=False,
        )

    def resolvable(self, sha: str) -> bool:
        if not sha or not self.available:
            return False
        if sha not in self._resolved:
            self._resolved[sha] = (
                self._run("cat-file", "-e", f"{sha}^{{commit}}").returncode == 0
            )
        return self._resolved[sha]

    def same(self, a: str, b: str) -> bool:
        ra = self._run("rev-parse", f"{a}^{{commit}}")
        rb = self._run("rev-parse", f"{b}^{{commit}}")
        return (
            ra.returncode == 0
            and rb.returncode == 0
            and ra.stdout.strip() == rb.stdout.strip()
        )

    def is_ancestor(self, older: str, newer: str) -> bool:
        # THE primitive this gate is built on. `--is-ancestor` exits 0 when
        # `older` is reachable from `newer` (and for an identical commit).
        return self._run("merge-base", "--is-ancestor", older, newer).returncode == 0


def classify(git: Git, earlier: dict, newest: dict) -> str:
    """How does an earlier row's tree relate to the newest row's tree?"""
    a, b = earlier["solver_commit"], newest["solver_commit"]
    if not git.available:
        return "no-git"
    if not git.resolvable(a) or not git.resolvable(b):
        return "unresolvable"
    if git.same(a, b):
        return "same"
    if git.is_ancestor(a, b):
        return "ok"
    if git.is_ancestor(b, a):
        return "SUPERSEDED-BY-OLDER-CODE"
    return "DIVERGENT"


def main() -> int:
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("--ledger", default=str(DEFAULT_LEDGER))
    ap.add_argument(
        "--repo",
        default=str(ROOT),
        help="checkout the `solver commit` shas are resolved in; degrades to "
        "'no-git' (advisory) when this is not a checkout.",
    )
    args = ap.parse_args()

    ledger = Path(args.ledger)
    if not ledger.is_file():
        print(
            f"PARITY_ANCESTRY_ERROR|no ledger at {ledger}",
            file=sys.stderr,
        )
        return 2
    try:
        records = parse_ledger(ledger.read_text(encoding="utf-8"), str(ledger))
    except LedgerError as exc:
        print(f"PARITY_ANCESTRY_ERROR|{exc}", file=sys.stderr)
        return 2

    logics = sorted({r["logic"] for r in records})
    if len(logics) < MIN_LOGICS:
        print(
            f"PARITY_ANCESTRY_ERROR|parsed only {len(logics)} logic(s) from "
            f"{ledger} ({len(records)} entries). That is a broken parser or the "
            "wrong file, and a near-empty population would make this gate pass "
            "vacuously.",
            file=sys.stderr,
        )
        return 2

    git = Git(Path(args.repo))

    # Series in file order: (logic, reference) -> [valid rows].
    series: dict[tuple[str, str], list[dict]] = {}
    for r in records:
        if r["disagreements"] > 0:
            continue
        series.setdefault((r["logic"], r["reference"]), []).append(r)

    print(f"parity ledger commit ancestry — {ledger}")
    print(f"  repo: {args.repo}{'' if git.available else '  (NO GIT — advisory only)'}")
    print(
        f"  {'series':<22} {'rows':>4}  {'newest':<20} {'commit':<11} state"
    )

    broken: list[tuple[str, dict, dict, str]] = []
    unresolvable = 0
    no_git = 0
    ts_out_of_order: list[tuple[str, dict, dict]] = []
    detail: list[str] = []

    for key in sorted(series):
        logic, reference = key
        rows = series[key]
        name = logic + (f" [{reference}]" if reference else "")
        newest = rows[-1]

        # File order vs timestamp order. Advisory: see this script's header.
        for prev, cur in zip(rows, rows[1:]):
            if cur["ts"] < prev["ts"]:
                ts_out_of_order.append((name, prev, cur))

        states: list[str] = []
        for earlier in rows[:-1]:
            st = classify(git, earlier, newest)
            states.append(st)
            if st == "unresolvable":
                unresolvable += 1
            elif st == "no-git":
                no_git += 1
            elif st in ("SUPERSEDED-BY-OLDER-CODE", "DIVERGENT"):
                broken.append((name, earlier, newest, st))
                detail.append(
                    f"  {st}: {name} newest row at {ledger}:{newest['line']} "
                    f"({newest['ts']:%Y-%m-%dT%H:%MZ}, {newest['solved']}, "
                    f"`{newest['solver_commit']}`) is NOT a descendant of the "
                    f"row at {ledger}:{earlier['line']} "
                    f"({earlier['ts']:%Y-%m-%dT%H:%MZ}, {earlier['solved']}, "
                    f"`{earlier['solver_commit']}`)"
                )

        bad = [s for s in states if s in ("SUPERSEDED-BY-OLDER-CODE", "DIVERGENT")]
        if bad:
            state = f"{'/'.join(sorted(set(bad)))} x{len(bad)}"
        elif "unresolvable" in states or "no-git" in states:
            state = "ok (some rows unresolvable — advisory)"
        elif not states:
            state = "ok (single row)"
        else:
            state = "ok"
        print(
            f"  {name:<22} {len(rows):>4}  {newest['ts']:%Y-%m-%dT%H:%MZ}  "
            f"{newest['solver_commit'][:9] or '?':<11} {state}"
        )

    for name, prev, cur in ts_out_of_order:
        print(
            f"  note: OUT-OF-ORDER-TIMESTAMP {name}: row at {ledger}:{cur['line']} "
            f"({cur['ts']:%Y-%m-%dT%H:%MZ}) was appended after "
            f"{ledger}:{prev['line']} ({prev['ts']:%Y-%m-%dT%H:%MZ}) — the two "
            "sweeps overlapped in time (advisory)"
        )

    print(
        "PARITY_ANCESTRY"
        f"|series={len(series)}"
        f"|rows={sum(len(v) for v in series.values())}"
        f"|unordered_series={len({b[0] for b in broken})}"
        f"|unordered_pairs={len(broken)}"
        f"|unresolvable_pairs={unresolvable}"
        f"|no_git_pairs={no_git}"
        f"|out_of_order_timestamps={len(ts_out_of_order)}"
        f"|verdict={'FAIL' if broken else 'PASS'}"
    )

    if broken:
        print("", file=sys.stderr)
        for line in detail:
            print(line, file=sys.stderr)
        print("", file=sys.stderr)
        for name in sorted({b[0] for b in broken}):
            print(
                f"PARITY_ANCESTRY_ERROR|{name}: the board's newest row was not "
                "measured on a tree containing every earlier row's tree, so it "
                "is not a statement about the current state of that division",
                file=sys.stderr,
            )
        print("", file=sys.stderr)
        print(
            "  The remedy is to re-measure from a commit that descends from "
            "both trees (in practice: current origin/main) and APPEND:",
            file=sys.stderr,
        )
        print(
            "    cargo build --release -p axeyum-bench --example smtcomp_cli",
            file=sys.stderr,
        )
        for name in sorted({b[0] for b in broken}):
            print(f"    scripts/parity-run.sh {name.split(' ')[0]}", file=sys.stderr)
        print(
            "  Do NOT edit or remove the older row. The ledger is append-only "
            "so a number that went down stays visible.",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
