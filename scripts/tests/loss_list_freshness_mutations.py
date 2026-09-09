#!/usr/bin/env python3
"""Mutation controls for `scripts/check-loss-list-freshness.py`.

Breaks one guard at a time, runs `scripts/tests/test-check-loss-list-freshness.sh`
against the mutant, and prints which cases died. The suite's header claims a
mutation table; this is the thing that makes that claim a measurement rather
than a comment.

A mutation that kills NOTHING is the finding: it means the guard it broke is
either dead code or has no control, and the suite is measuring the maintainer's
memory rather than the checker.

Run from the repository root:  python3 scripts/tests/loss_list_freshness_mutations.py
"""

from __future__ import annotations

import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
TARGET = ROOT / "scripts" / "check-loss-list-freshness.py"
SUITE = ROOT / "scripts" / "tests" / "test-check-loss-list-freshness.sh"

# name -> (needle, replacement). Each must apply exactly once.
MUTATIONS: dict[str, tuple[str, str]] = {
    "per-division-authority-collapsed": (
        "    for entry in live:\n        for div in entry[\"divisions\"]:\n"
        "            authority[div] = entry",
        "    for div in {d for e in live for d in e[\"divisions\"]}:\n"
        "        authority[div] = newest_overall",
    ),
    "superseded-by-requirement-removed": (
        "            if not m:\n                flags.append(\"UNSUPERSEDED\")",
        "            if False:\n                flags.append(\"UNSUPERSEDED\")",
    ),
    "superseded-by-target-check-removed": (
        "                if named not in {e[\"name\"] for e in live}:",
        "                if False:",
    ),
    "self-supersession-check-removed": (
        "                elif named == entry[\"name\"]:",
        "                elif False:",
    ),
    "age-fail-removed": (
        "            if age > max_days:\n                problems.append(",
        "            if False:\n                problems.append(",
    ),
    "warn-band-collapsed": (
        "        if current and warn_days < age <= max_days:",
        "        if False:",
    ),
    "required-manifest-fields-emptied": (
        'REQUIRED_MANIFEST_FIELDS = ("as_of", "solver_commit", "binary_sha256", "budget_s")',
        "REQUIRED_MANIFEST_FIELDS = ()",
    ),
    "no-manifest-branch-removed": (
        '    if not path.exists():\n        return None, "no MANIFEST.json"',
        "    if not path.exists():\n        return {}, None",
    ),
    "unrecorded-reason-check-removed": (
        'UNRECORDED_RE = re.compile(r"^unrecorded:\\s*\\S.{19,}", re.DOTALL)',
        'UNRECORDED_RE = re.compile(r"", re.DOTALL)',
    ),
    "min-sets-zero": ("MIN_SETS = 1", "MIN_SETS = 0"),
    "currency-made-fatal": (
        "        detail_currency = None\n",  # placeholder, patched below
        "",
    ),
    "division-re-relaxed": (
        'DIVISION_RE = re.compile(r"^[A-Z][A-Z0-9_]*$")',
        'DIVISION_RE = re.compile(r"^.*$")',
    ),
}

# `currency-made-fatal` is not a one-line swap: it has to turn an advisory
# string into a problem. Expressed as a regex append instead.
CURRENCY_FATAL = (
    re.compile(
        r"(        currency = solver_currency\(\n"
        r"            root, \(manifest or \{\}\)\.get\(\"solver_commit\"\) if manifest else None\n"
        r"        \)\n)"
    ),
    "\\1        problems.append(f\"{entry['name']}: currency {currency}\")\n",
)


def run_suite() -> tuple[int, set[str]]:
    proc = subprocess.run(
        ["bash", str(SUITE)], capture_output=True, text=True, cwd=str(ROOT), check=False
    )
    dead = {
        line.split("case:")[1].split()[0]
        for line in proc.stdout.splitlines()
        if line.startswith("FAIL case:")
    }
    return proc.returncode, dead


def main() -> int:
    original = TARGET.read_text()

    rc, dead = run_suite()
    if rc != 0 or dead:
        print(f"BASELINE IS RED (rc={rc}, dead={sorted(dead)}) -- fix that first.")
        return 1
    print("baseline: suite green\n")

    backup = Path(tempfile.mkdtemp()) / "check-loss-list-freshness.py"
    shutil.copy2(TARGET, backup)

    findings: list[tuple[str, set[str]]] = []
    ok = True
    try:
        for name, (needle, repl) in MUTATIONS.items():
            if name == "currency-made-fatal":
                pat, sub = CURRENCY_FATAL
                mutated, n = pat.subn(sub, original)
                if n != 1:
                    print(f"SKIP {name}: anchor matched {n} times, not 1")
                    ok = False
                    continue
            else:
                if original.count(needle) != 1:
                    print(
                        f"SKIP {name}: anchor matched {original.count(needle)} "
                        f"times, not 1 -- the anchor has drifted from the source"
                    )
                    ok = False
                    continue
                mutated = original.replace(needle, repl)
            TARGET.write_text(mutated)
            rc, killed = run_suite()
            findings.append((name, killed))
            if not killed:
                ok = False
                print(f"  !! {name:<40} killed NOTHING -- unguarded")
            else:
                print(f"     {name:<40} killed {', '.join(sorted(killed))}")
    finally:
        shutil.copy2(backup, TARGET)

    print()
    rc, dead = run_suite()
    if rc != 0:
        print("RESTORE FAILED: the suite is red after restoring the original.")
        return 1
    print("restored: suite green")
    print()
    print(f"{len(findings)} mutations, {sum(1 for _, k in findings if k)} killed")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
