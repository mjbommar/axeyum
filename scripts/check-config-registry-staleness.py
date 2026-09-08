#!/usr/bin/env python3
"""Flag registry entries whose justification predates the code it protects.

This is the check the config registry exists for. `MAX_ONLINE_LRA_ATOMS` rested
on a measurement taken 2026-08-03 of an 8 GiB abort; `MAX_LRA_CACHED_COEFFICIENTS`,
the bound that caps exactly that cost, landed 2026-08-06 — three days later. The
measurement described a tree in which the thing it protected against was
unbounded, and it stood for thirteen months because nothing could compare a date
against a diff.

For every DATED entry in `crates/axeyum-solver/src/config_registry.rs`, this asks
git whether anything the justification `rests_on` changed strictly after the day
that measurement was taken. If so, the measurement describes a tree that no
longer exists and the entry is STALE.

    exit 0  no dated entry is stale
    exit 1  at least one dated entry is stale   <- the finding
    exit 2  the registry could not be read, or a self-check failed

`--list` prints the whole registry (dated and undated) and exits 0; use it to
see the surface rather than to gate on it.

WHY `git log -G` AND NOT A FILE MTIME: a file's mtime says nothing after a fresh
clone, and a whole-file `git log` on a 9,000-line dispatcher is stale every day
for reasons that have nothing to do with the bound. `-G<symbol>` matches commits
whose DIFF mentions the symbol, which is the closest available proxy for "the
code this measurement was about changed".

WHAT IT CANNOT SEE: a semantic dependency nobody wrote down. The check is only
as good as each entry's `rests_on`, which is why an entry may not be dated
without naming one (enforced by `dated_justifications_are_well_formed`). A
justification that rests on nothing cannot go stale, so it would be a date that
means nothing.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
REGISTRY_RS = REPO / "crates" / "axeyum-solver" / "src" / "config_registry.rs"

ENTRY_RE = re.compile(r"^    ConfigEntry \{$")
# `re.MULTILINE` is load-bearing: this is applied to a multi-line blob, and
# without it `^`/`$` anchor to the whole string, every field silently fails to
# match, and the parser returns zero entries. The self-check in `main` caught
# exactly that on this script's first run — a "0 stale" report that would
# otherwise have been indistinguishable from a clean bill of health.
FIELD_RE = re.compile(r"^\s{8}(\w+):\s*(.*?),?$", re.MULTILINE)
STR_RE = re.compile(r'^"((?:[^"\\]|\\.)*)"')
# The `\s*,?\s*` before the closing paren is load-bearing: rustfmt breaks a
# multi-argument `sym(...)` across lines AND adds a trailing comma, so a regex
# ending in `\s*\)` matches nothing. Without it every dated entry parsed with an
# EMPTY `rests_on`, and the checker reported "no dated justification is stale"
# for all 24 of them — a checker that could not fire, printing exactly what a
# working one prints. The positive control below is what caught it.
SYM_RE = re.compile(
    r'sym\(\s*"((?:[^"\\]|\\.)*)"\s*,\s*"((?:[^"\\]|\\.)*)"\s*,?\s*\)'
)
FILE_RE = re.compile(r'file\(\s*"((?:[^"\\]|\\.)*)"\s*,?\s*\)')


@dataclass
class Entry:
    name: str = ""
    module: str = ""
    value: str = ""
    unit: str = ""
    location: str = ""
    measured_on: str | None = None
    measured_at_commit: str | None = None
    rests_on: list[tuple[str, str | None]] = field(default_factory=list)

    @property
    def key(self) -> str:
        return f"{self.module}::{self.name}"


def _unquote(s: str) -> str:
    m = STR_RE.match(s.strip())
    return m.group(1).replace('\\"', '"').replace("\\\\", "\\") if m else ""


def parse_registry(path: Path) -> list[Entry]:
    """Parse the `ConfigEntry` literals out of the registry source.

    Deliberately structural rather than clever: a `ConfigEntry {` line opens an
    entry and the matching `    },` closes it. The count is cross-checked against
    the raw literal count below, so a parse that silently skipped an entry is a
    self-check failure rather than a quietly shorter report.
    """
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    entries: list[Entry] = []
    i = 0
    while i < len(lines):
        if not ENTRY_RE.match(lines[i]):
            i += 1
            continue
        e = Entry()
        i += 1
        depth = 1
        buf: list[str] = []
        while i < len(lines) and depth > 0:
            line = lines[i]
            if line.rstrip() == "    },":
                depth = 0
                break
            buf.append(line)
            i += 1
        blob = "\n".join(buf)
        for m in FIELD_RE.finditer(blob):
            k, v = m.group(1), m.group(2)
            if k == "name":
                e.name = _unquote(v)
            elif k == "module":
                e.module = _unquote(v)
            elif k == "value":
                e.value = _unquote(v)
            elif k == "unit":
                e.unit = _unquote(v)
        # `undated("loc")` or a multi-line `dated(...)` call.
        und = re.search(r'undated\(\s*"((?:[^"\\]|\\.)*)"\s*\)', blob)
        if und:
            e.location = und.group(1)
        else:
            dated = re.search(r"justification: dated\(\s*\n(.*?)\n\s{8}\),", blob, re.S)
            if dated:
                body = dated.group(1)
                strs = re.findall(r'"((?:[^"\\]|\\.)*)"', body.split("&[")[0])
                if len(strs) >= 2:
                    e.location, e.measured_on = strs[0], strs[1]
                if len(strs) >= 3:
                    e.measured_at_commit = strs[2]
                deps_part = body.split("&[", 1)[1] if "&[" in body else ""
                for p, s in SYM_RE.findall(deps_part):
                    e.rests_on.append((p, s))
                for p in FILE_RE.findall(deps_part):
                    e.rests_on.append((p, None))
        if e.name and e.module:
            entries.append(e)
        i += 1
    return entries


def introducing_commit(path: str, symbol: str | None) -> str | None:
    """The oldest commit whose diff to `path` mentions `symbol`.

    Used to exclude a constant's OWN introduction from its OWN staleness; see
    the narrow exclusion in `main`.
    """
    cmd = ["git", "-C", str(REPO), "log", "--reverse", "--format=%h"]
    if symbol:
        cmd.append(f"-G{re.escape(symbol)}")
    cmd += ["--", path]
    out = subprocess.run(cmd, capture_output=True, text=True, check=False)
    if out.returncode != 0:
        return None
    shas = out.stdout.split()
    return shas[0] if shas else None


def commits_after(date: str, path: str, symbol: str | None) -> list[tuple[str, str, str]]:
    """Commits touching `path` strictly after `date`, optionally mentioning `symbol`.

    `--after "<date> 23:59:59"` rather than `--since=<date>`: a commit landing on
    the same day as the measurement is not evidence the measurement is stale, and
    `--since` would flag every entry dated today against its own landing commit.
    """
    cmd = [
        "git", "-C", str(REPO), "log",
        "--after", f"{date} 23:59:59",
        "--format=%h\t%cs\t%s",
    ]
    if symbol:
        cmd.append(f"-G{re.escape(symbol)}")
    cmd += ["--", path]
    out = subprocess.run(cmd, capture_output=True, text=True, check=False)
    if out.returncode != 0:
        raise RuntimeError(f"git log failed for {path}: {out.stderr.strip()}")
    rows = []
    for line in out.stdout.splitlines():
        parts = line.split("\t", 2)
        if len(parts) == 3:
            rows.append((parts[0], parts[1], parts[2]))
    return rows


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--list", action="store_true", help="print the registry and exit 0")
    ap.add_argument("--verbose", action="store_true", help="name the commits that made an entry stale")
    ap.add_argument(
        "--registry",
        type=Path,
        default=REGISTRY_RS,
        help="registry source to read (default: the in-tree one). Exists so this "
             "check's own POSITIVE CONTROL can be run against a deliberately "
             "backdated copy without mutating a shared checkout. A staleness "
             "checker that has never been shown to fire is indistinguishable "
             "from one that cannot.",
    )
    args = ap.parse_args()

    registry_rs = args.registry
    if not registry_rs.exists():
        print(f"FAIL: registry not found at {registry_rs}", file=sys.stderr)
        return 2

    entries = parse_registry(registry_rs)

    # Self-check: the parser must find every `ConfigEntry` literal in the file.
    # A parse that silently dropped entries would report "0 stale" for a reason
    # that has nothing to do with staleness, which is the shape of checker this
    # repository has been bitten by. The needle is split so this line does not
    # count itself.
    needle = "    ConfigEntry" + " {"
    literals = registry_rs.read_text(encoding="utf-8").count(needle)
    if literals != len(entries):
        print(
            f"FAIL (self-check): the file holds {literals} ConfigEntry literals "
            f"but the parser produced {len(entries)} entries. The report below "
            f"would be silently incomplete.",
            file=sys.stderr,
        )
        return 2

    dated = [e for e in entries if e.measured_on]
    undated = [e for e in entries if not e.measured_on]

    if args.list:
        for e in sorted(entries, key=lambda x: x.key):
            when = e.measured_on or "UNDATED"
            print(f"{when}\t{e.key}\t= {e.value}\t[{e.unit}]\t{e.location}")
        print(f"\n{len(entries)} entries, {len(dated)} dated, {len(undated)} undated",
              file=sys.stderr)
        return 0

    stale: list[tuple[Entry, str, str | None, list[tuple[str, str, str]]]] = []
    for e in dated:
        for path, symbol in e.rests_on:
            if not (REPO / path).exists():
                print(f"FAIL: {e.key} rests on a missing path {path}", file=sys.stderr)
                return 2
            rows = commits_after(e.measured_on, path, symbol)
            # A constant's OWN introducing commit cannot make its OWN
            # justification stale: a decision is recorded, then the code
            # implementing it lands, and that ordering is the healthy one.
            # Measured: ADR-0360 is dated 2026-07-22 and `5b4c5b404` INTRODUCED
            # all three `MAX_MBQI_FREE_INT_*` constants on 2026-07-23. This
            # check reported those as three stale entries on its first honest
            # run. They are not stale; the rule was.
            #
            # The exclusion is deliberately NARROW — self-dependency only. A
            # commit that introduces a DIFFERENT constant an entry rests on is
            # exactly the failure this check exists for: `96ff85930` INTRODUCED
            # `MAX_LRA_CACHED_COEFFICIENTS`, and that introduction is what
            # falsified `MAX_ONLINE_LRA_ATOMS`'s 2026-08-03 measurement.
            # Excluding introductions in general would blind this checker to its
            # own founding example, which the positive control would then catch.
            if path == e.module and symbol == e.name:
                intro = introducing_commit(path, symbol)
                if intro:
                    rows = [r for r in rows if r[0] != intro]
            if rows:
                stale.append((e, path, symbol, rows))

    print(f"config registry: {len(entries)} entries, {len(dated)} dated, "
          f"{len(undated)} undated ({100 * len(undated) // max(len(entries), 1)}%).")

    if not stale:
        print(f"No dated justification is stale: nothing any of the {len(dated)} "
              f"dated entries rests on has changed since it was measured.")
        return 0

    print(f"\nSTALE: {len(stale)} dated justification(s) predate a change to the "
          f"code they protect.\n")
    for e, path, symbol, rows in stale:
        what = f"{path}::{symbol}" if symbol else path
        print(f"  {e.key}")
        print(f"    measured {e.measured_on} ({e.location}), rests on {what}")
        print(f"    but {what} changed {len(rows)} time(s) since:")
        for h, d, s in rows[: (None if args.verbose else 3)]:
            print(f"      {h} {d} {s[:96]}")
        if not args.verbose and len(rows) > 3:
            print(f"      ... {len(rows) - 3} more (--verbose)")
        print()
    print("Re-take the measurement, or narrow the entry's `rests_on` if the "
          "change cannot affect it. Do NOT simply move the date.")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
