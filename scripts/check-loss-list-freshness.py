#!/usr/bin/env python3
"""check-loss-list-freshness.py -- is the loss population a lane is briefed
against the CURRENT one?

WHY THIS EXISTS
---------------
`bench-results/parity-losses-<YYYYMMDD>/<DIV>.txt` is the population every
optimisation brief in this repository is written against: "the N files we lose
in <DIV>".  Measured 2026-09-08, **141 of the 403 files** on the 2026-09-05
lists were already decided by the shipped default -- QF_UFLIA had gone
122 -> 151 solved, QF_LIA 113 -> 119, QF_LRA 93 -> 97, QF_ABV 179 -> 186 in
three days.  Several lanes had already been dispatched at files the tree wins.

Nothing was wrong with the lists.  They were a correct measurement of
2026-09-05, sitting in a directory whose name says so, and every reader --
including the people who cut them -- treated them as current anyway.  A date in
a path is not a staleness signal; it is a fact a reader has to *decide* to act
on, and readers reliably do not.

So this gate makes the decision mechanical.  It does not re-measure -- it is
cheap, it reads committed files -- it only makes "you are reading a superseded
population" impossible to miss.

THE UNIT IS A DIVISION, NOT A SET
----------------------------------
The first version of this gate treated the newest *directory* as the authority
and failed every older one.  That was wrong the moment it ran: the 2026-09-06
set is a QF_NRA-only census, an ADDITION to the eleven-division 2026-09-05 set,
not a replacement for it.  A per-set rule would have demanded that the eleven
divisions declare themselves superseded by a set that never measured them.

So authority is per division: for each `<DIV>`, the newest set carrying a
`<DIV>.txt` is the one a brief should cite, and every older set carrying that
division is history for it.  A set can be simultaneously the authority for one
division and superseded for another, which is exactly what the tree looks like.

WHAT IT CHECKS (and why each is the shape it is)
------------------------------------------------
  1. SUPERSESSION.  A set that is no longer the authority for at least one of
     its divisions must carry a `SUPERSEDED-BY:` line in its own `README.md`
     naming the set that replaced it.  This is the guard that cannot rot: the
     moment a lane cuts a new set, this gate is red until the old one is
     marked, and the mark lands in the file a reader opens.

     It deliberately does NOT touch the lists' bytes.  An old list is the
     record of what was true that day and stays byte-identical; the banner goes
     in the README beside it.

  2. AGE, per division, against a budget (default: FAIL > 14 days, WARN > 10)
     applied to that division's AUTHORITY set.  The budget matches
     `check-parity-freshness.py`'s and for the reason argued there at length --
     it is the fifteen-day window this repository actually lost.  A loss list
     is downstream of a parity sweep, so it can never be fresher than the
     ledger that sweep writes; a tighter budget here would red this gate for a
     condition the parity gate owns.

  3. MANIFEST completeness.  A set must record, in `MANIFEST.json`, the solver
     commit it was cut at, the sha256 of the binary that cut it, the per-file
     budget, and the as-of date.  Without the commit, point 4 is unanswerable
     and "was fix X in this measurement?" is a memory question again.

     A field that is genuinely unrecoverable is written `unrecorded: <reason>`
     and accepted.  An absent field and an unknowable one are different
     findings, and a gate that cannot tell them apart teaches lanes to invent a
     value.

  4. SOLVER CURRENCY -- ADVISORY, never fatal.  `behind=N` commits touching
     `crates/` between the recorded solver commit and HEAD, plus whether that
     sha resolves here and whether it is an ancestor.

     Advisory for the three reasons `check-parity-freshness.py` sets out and
     this gate does not restate: velocity here is bursty, so any fixed
     `behind=` ceiling is red-by-construction during a burst; non-ancestry is
     legitimate because lanes measure from their own worktrees; and a sha can
     vanish from a shared checkout entirely.  What `behind=` is FOR is putting
     `git merge-base --is-ancestor <solver-commit> <fix>` one command away.

WHAT THIS GATE CANNOT TELL YOU
-------------------------------
Whether the newest list is RIGHT.  A set cut today from a tree missing a
one-file fix worth +22 files is fresher-looking and more wrong than the set it
replaces.  Freshness is not correctness; this measures only the first, and
`behind=` is the handle on the second.

WHAT TO DO WHEN THIS REDS
-------------------------
  * `not superseded` -- add the banner.  One line in the old set's README.
  * `stale` -- re-cut that division, then mark the previous set superseded.
    `bench-results/parity-losses-20260908/scripts/run-all.sh` is the runner.
  * `manifest` -- the set was cut without recording what cut it.  Record it, or
    write `unrecorded: <why>` if it is genuinely gone.

Exit 0 clean/warn, 1 on any stale / unsuperseded / malformed set, 2 on usage.

Env:
  AXEYUM_LOSS_LIST_MAX_AGE_DAYS   fail budget in days (default 14)
  AXEYUM_LOSS_LIST_WARN_AGE_DAYS  warn budget in days (default 10)
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import re
import subprocess
import sys
from pathlib import Path

# `parity-losses-YYYYMMDD`, optionally with a trailing qualifier so a lane can
# cut a partial or per-division set without it silently becoming "the newest".
SET_RE = re.compile(r"^parity-losses-(\d{8})(?:-([A-Za-z0-9._-]+))?$")

SUPERSEDED_RE = re.compile(r"^\s*SUPERSEDED-BY:\s*(\S+)", re.MULTILINE)

# A division list is `<DIV>.txt` where `<DIV>` is a logic name. Upper case is
# not decoration: helper `.txt` files (`abv-watchdog-blind.txt`,
# `UF.axeyum-only24.ab.txt`) live in these directories and are not populations.
DIVISION_RE = re.compile(r"^[A-Z][A-Z0-9_]*$")

REQUIRED_MANIFEST_FIELDS = ("as_of", "solver_commit", "binary_sha256", "budget_s")

UNRECORDED_RE = re.compile(r"^unrecorded:\s*\S.{19,}", re.DOTALL)

# A scan that stopped matching its subject returns the same empty answer as a
# clean tree. Refuse the empty answer rather than pass on it.
MIN_SETS = 1


def discover_sets(root: Path) -> list[dict]:
    bench = root / "bench-results"
    out: list[dict] = []
    if not bench.is_dir():
        return out
    for child in sorted(bench.iterdir()):
        if not child.is_dir():
            continue
        m = SET_RE.match(child.name)
        if not m:
            continue
        day, qualifier = m.group(1), m.group(2)
        try:
            as_of_path = dt.datetime.strptime(day, "%Y%m%d").replace(
                tzinfo=dt.timezone.utc
            )
        except ValueError:
            out.append(
                {
                    "dir": child,
                    "name": child.name,
                    "error": f"directory name carries an impossible date: {day}",
                    "divisions": [],
                }
            )
            continue
        divisions = sorted(
            p.name[:-4]
            for p in child.glob("*.txt")
            if p.stat().st_size and DIVISION_RE.fullmatch(p.name[:-4])
        )
        out.append(
            {
                "dir": child,
                "name": child.name,
                "as_of_path": as_of_path,
                "qualifier": qualifier,
                "divisions": divisions,
                "error": None,
            }
        )
    return out


def read_manifest(entry: dict) -> tuple[dict | None, str | None]:
    path = entry["dir"] / "MANIFEST.json"
    if not path.exists():
        return None, "no MANIFEST.json"
    try:
        data = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        return None, f"unreadable MANIFEST.json ({exc})"
    missing = [f for f in REQUIRED_MANIFEST_FIELDS if not str(data.get(f, "")).strip()]
    if missing:
        return data, "MANIFEST.json missing " + ", ".join(missing)
    bare = [
        f
        for f in REQUIRED_MANIFEST_FIELDS
        if str(data[f]).strip().startswith("unrecorded")
        and not UNRECORDED_RE.match(str(data[f]).strip())
    ]
    if bare:
        return data, (
            "MANIFEST.json marks " + ", ".join(bare) + " `unrecorded` with no "
            "reason -- write `unrecorded: <why it is unrecoverable>`"
        )
    return data, None


def git(root: Path, *args: str) -> tuple[int, str]:
    try:
        proc = subprocess.run(
            ["git", "-C", str(root), *args],
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError:
        return 127, ""
    return proc.returncode, proc.stdout.strip()


def solver_currency(root: Path, sha: str | None) -> str:
    """ADVISORY. Never contributes to the exit status -- see the header."""
    if not sha:
        return "commit=absent"
    sha = str(sha).strip()
    if sha.startswith("unrecorded"):
        return "commit=unrecorded"
    code, _ = git(root, "rev-parse", "--git-dir")
    if code != 0:
        return f"commit={sha[:10]} (no git checkout here)"
    code, resolved = git(root, "rev-parse", "--verify", f"{sha}^{{commit}}")
    if code != 0:
        return f"commit={sha[:10]} UNRESOLVABLE in this checkout"
    code, _ = git(root, "merge-base", "--is-ancestor", resolved, "HEAD")
    ancestry = "ancestor-of-HEAD" if code == 0 else "NOT-an-ancestor-of-HEAD"
    code, out = git(root, "rev-list", "--count", f"{resolved}..HEAD", "--", "crates/")
    behind = out if code == 0 and out else "?"
    return f"commit={sha[:10]} {ancestry} behind={behind}"


def manifest_as_of(entry: dict, manifest: dict | None) -> tuple[dt.datetime, str | None]:
    if manifest and str(manifest.get("as_of", "")).strip():
        try:
            when = dt.datetime.fromisoformat(
                str(manifest["as_of"]).replace("Z", "+00:00")
            )
            if when.tzinfo is None:
                when = when.replace(tzinfo=dt.timezone.utc)
            return when, None
        except ValueError:
            return entry["as_of_path"], "MANIFEST.json as_of is not an ISO date"
    return entry["as_of_path"], None


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", default=None)
    ap.add_argument("--max-age-days", type=float, default=None)
    ap.add_argument("--warn-age-days", type=float, default=None)
    ap.add_argument("--now", default=None, help="ISO date, for controls")
    args = ap.parse_args()

    root = Path(args.root) if args.root else Path(__file__).resolve().parent.parent
    max_days = (
        args.max_age_days
        if args.max_age_days is not None
        else float(os.environ.get("AXEYUM_LOSS_LIST_MAX_AGE_DAYS", "14"))
    )
    warn_days = (
        args.warn_age_days
        if args.warn_age_days is not None
        else float(os.environ.get("AXEYUM_LOSS_LIST_WARN_AGE_DAYS", "10"))
    )
    now = (
        dt.datetime.fromisoformat(args.now).replace(tzinfo=dt.timezone.utc)
        if args.now
        else dt.datetime.now(dt.timezone.utc)
    )

    sets = discover_sets(root)
    problems: list[str] = []
    for entry in sets:
        if entry.get("error"):
            problems.append(f"{entry['name']}: {entry['error']}")

    live = [e for e in sets if not e.get("error") and e["divisions"]]
    if len(live) < MIN_SETS:
        print(
            "loss-list freshness: found NO `bench-results/parity-losses-*` set\n"
            "  carrying division lists. A scan that stopped matching its subject\n"
            "  reports the same empty answer as a clean tree, so this is a\n"
            "  FAILURE, not a pass.",
            file=sys.stderr,
        )
        return 1

    live.sort(key=lambda e: (e["as_of_path"], e["name"]))
    newest_overall = live[-1]

    # Per-division authority: the newest set carrying that division.
    authority: dict[str, dict] = {}
    for entry in live:
        for div in entry["divisions"]:
            authority[div] = entry

    manifests: dict[str, tuple[dict | None, str | None]] = {}
    for entry in live:
        manifests[entry["name"]] = read_manifest(entry)

    print(f"loss-list freshness: {len(live)} set(s), {len(authority)} division(s)")
    print(f"  budget: warn > {warn_days:g}d, FAIL > {max_days:g}d (per division)")
    print()

    # --- per-set report -----------------------------------------------------
    for entry in live:
        manifest, manifest_err = manifests[entry["name"]]
        as_of, as_of_err = manifest_as_of(entry, manifest)
        manifest_err = manifest_err or as_of_err
        age = (now - as_of).total_seconds() / 86400.0
        current = [d for d in entry["divisions"] if authority[d] is entry]
        stale_divs = [d for d in entry["divisions"] if authority[d] is not entry]

        flags: list[str] = []
        if manifest_err:
            flags.append("MALFORMED")
            problems.append(f"{entry['name']}: {manifest_err}")

        if stale_divs:
            readme = entry["dir"] / "README.md"
            text = readme.read_text() if readme.exists() else ""
            m = SUPERSEDED_RE.search(text)
            if not m:
                flags.append("UNSUPERSEDED")
                problems.append(
                    f"{entry['name']}: {len(stale_divs)} of its "
                    f"{len(entry['divisions'])} divisions have been re-cut "
                    f"({', '.join(stale_divs)}) but its README.md carries no "
                    f"`SUPERSEDED-BY:` line -- a lane reading it cannot see that "
                    f"it is history"
                )
            else:
                named = Path(m.group(1).strip().rstrip("/.,`")).name
                if named not in {e["name"] for e in live}:
                    flags.append("MISDIRECTED")
                    problems.append(
                        f"{entry['name']}: SUPERSEDED-BY names `{named}`, which "
                        f"is not a loss-list set in this checkout"
                    )
                elif named == entry["name"]:
                    flags.append("MISDIRECTED")
                    problems.append(
                        f"{entry['name']}: SUPERSEDED-BY names itself"
                    )
                else:
                    flags.append(f"superseded-by {named}")

        for div in current:
            if age > max_days:
                problems.append(
                    f"{entry['name']}/{div}: the current loss population for this "
                    f"division is {age:.1f} days old, past the {max_days:g}-day budget"
                )
        if current and warn_days < age <= max_days:
            flags.append("WARN-AGE")

        state = "ok" if not flags else " ".join(flags)
        currency = solver_currency(
            root, (manifest or {}).get("solver_commit") if manifest else None
        )
        print(f"  {entry['name']:<32} {age:6.1f}d  {len(entry['divisions']):2d} lists")
        print(f"      state: {state}")
        print(f"      {currency}")
        if current:
            print(f"      authority for: {', '.join(current)}")
        if stale_divs:
            print(f"      history for:   {', '.join(stale_divs)}")

    # --- the table a brief-writer actually needs ----------------------------
    print()
    print("  cite these, per division:")
    total_files = 0
    stalest = 0.0
    for div in sorted(authority):
        entry = authority[div]
        manifest, _ = manifests[entry["name"]]
        as_of, _ = manifest_as_of(entry, manifest)
        age = (now - as_of).total_seconds() / 86400.0
        stalest = max(stalest, age)
        path = entry["dir"] / f"{div}.txt"
        n = sum(1 for line in path.read_text().splitlines() if line.strip())
        total_files += n
        mark = "STALE" if age > max_days else ("warn" if age > warn_days else "")
        print(f"    {div:<10} {n:4d} files  {entry['name']}  ({age:.1f}d) {mark}")
    print(f"    {'TOTAL':<10} {total_files:4d} files")
    print()
    print("  solver currency is ADVISORY and never fails this gate.")

    print(
        "loss-list-freshness"
        f"|sets={len(live)}"
        f"|divisions={len(authority)}"
        f"|files={total_files}"
        f"|newest={newest_overall['name']}"
        f"|stalest_days={stalest:.1f}"
        f"|problems={len(problems)}"
        f"|max_days={max_days:g}"
        f"|warn_days={warn_days:g}"
    )

    if problems:
        print()
        print("FAIL:", file=sys.stderr)
        for p in problems:
            print(f"  - {p}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
