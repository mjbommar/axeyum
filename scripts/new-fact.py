#!/usr/bin/env python3
"""Scaffold a fact whose evidence has been PROVED able to fail, before it exists.

Recording a result is the expensive step in this repository's cycle. Writing the
fact JSON by hand is ninety lines of boilerplate, and the part that actually
matters -- that each `checker_command` exits non-zero when the finding is not
there -- is done by eye, if at all. CLAUDE.md's measurement: **40 of 162 checker
runs across 36 settled facts exit 0 on completion alone**, and that set included
the inventory asserting axiom-freedom, this project's headline claim.

So this does not merely emit JSON. It runs the command, then attacks its own
patterns:

  1. every pattern must MATCH the real output (a typo'd regex is otherwise a
     checker that has never once been true);
  2. every pattern must FAIL on mutated output -- digits perturbed, `true` ->
     `false`, `0` -> `1` -- so a pattern that matches the surrounding prose
     rather than the finding is rejected here instead of in the ledger;
  3. `--require-count` pins a POPULATION. `grep -q` passes on one surviving row
     when the other four regressed, which is how a five-fixture claim becomes a
     one-fixture claim silently.

If any pattern survives every mutation, nothing is written and the pattern is
named. That is the whole point: a fact you cannot get out of this script is a
fact whose evidence would not have discriminated.

    scripts/new-fact.py --id F:my-result \\
      --title '...' --statement '...' \\
      --command 'cargo run -q -p axeyum-lean-kernel --example my_witness' \\
      --require 'trusted surface = 0 [(]empty[)]' \\
      --require-count '^law .* \\[\\]$=22'

# What it does NOT do

It does not judge whether the *statement* is true, whether the example measures
what its name says, or whether the pattern anchors on the interesting part of
the line. A pattern can discriminate and still be checking the wrong thing. It
also cannot invent `depends_on`; an isolated fact is a real cost (measured: 62
of 117 facts rest on nothing and support nothing) and this only warns.

Both streams are captured. A summary line on stderr with `2>/dev/null` matches
nothing and passes for the wrong reason -- a defect found in this ledger twice.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import shlex
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"


def matches(pattern: str, text: str) -> int:
    """How many lines `grep -cE` finds — the SAME ENGINE the ledger will run.

    Not Python's `re`. The emitted `checker_command` uses `grep -E`, and the two
    engines disagree on exactly the constructs this repository's checker
    commands are written with: `[[:space:]]` is a POSIX class to grep and a
    nested set to `re` (which warns and matches something else entirely). The
    first version of this script validated with `re`, so it rejected a pattern
    that grep accepts — a checker for checkers, checking a different language
    from the one that ships.
    """
    proc = subprocess.run(
        ["grep", "-cE", pattern], input=text, capture_output=True, text=True, check=False,
    )
    # grep exits 1 on "no match", which is not an error here.
    return int(proc.stdout.strip() or 0)


def run(command: str, timeout: int) -> tuple[int, str]:
    proc = subprocess.run(
        ["bash", "-c", command], cwd=ROOT, capture_output=True, text=True,
        timeout=timeout, check=False,
    )
    return proc.returncode, proc.stdout + proc.stderr


def mutants(text: str) -> list[tuple[str, str]]:
    """Plausible ways the finding could be absent while the prose survives.

    Deliberately crude and content-blind. A pattern that survives ALL of these
    is one that does not depend on any number or verdict in the output, which
    for a measurement is the definition of not discriminating.
    """
    out = [
        ("true->false", text.replace("true", "false")),
        ("digits+1", re.sub(r"\b(\d+)\b", lambda m: str(int(m.group(1)) + 1), text)),
        ("zeros->1", re.sub(r"\b0\b", "1", text)),
        ("empty-list->nonempty", text.replace("[]", "[X]")),
    ]
    return [(name, mutated) for name, mutated in out if mutated != text]


def check_pattern(
    pattern: str, want: int | None, text: str, allow_population_only: bool
) -> list[str]:
    """-> list of problems. Empty means the pattern matched and can fail."""
    problems: list[str] = []
    found = matches(pattern, text)
    if want is None:
        if found == 0:
            problems.append(
                f"pattern {pattern!r} matches NOTHING in the output; a checker "
                "that has never once been true is not a checker"
            )
            return problems
    elif found != want:
        problems.append(
            f"pattern {pattern!r} matched {found} time(s), --require-count says "
            f"{want}. Fix whichever is wrong before this reaches the ledger"
        )
        return problems

    all_mutants = mutants(text)
    survived = [
        name for name, mutated in all_mutants
        if (matches(pattern, mutated) == found and found > 0)
    ]
    if all_mutants and len(survived) == len(all_mutants):
        if want is None:
            problems.append(
                f"pattern {pattern!r} survives EVERY mutation of the output "
                f"({', '.join(survived)}), so it does not depend on any number or "
                "verdict the command reports. Anchor it on the finding, not the prose"
            )
        elif not allow_population_only:
            # A count check whose count no mutation moves is not worthless -- it
            # still fails when a row DISAPPEARS, which is the five-fixtures-became-one
            # regression. It just cannot see a value change inside a row that is
            # still there. That is a real distinction and the author should make it
            # deliberately, so it costs a flag rather than being waved through.
            problems.append(
                f"pattern {pattern!r} is POPULATION-ONLY: no mutation of the output "
                f"changes its match count ({found}). It will catch a row disappearing "
                "-- five fixtures becoming one -- and will NOT catch a value changing "
                "inside a row that is still there. Either pin the value literally "
                "(write the `0` or the `true` into the pattern) or pass "
                "--allow-population-only to say that is what you meant"
            )
    return problems


def command_for(command: str, pattern: str, want: int | None) -> str:
    """The `checker_command` as the ledger will store it."""
    quoted = shlex.quote(pattern)
    if want is None:
        return (
            f'out=$({command} 2>&1) && printf "%s\\n" "$out" | grep -qE {quoted}'
        )
    return (
        f'out=$({command} 2>&1) && '
        f'test "$(printf "%s\\n" "$out" | grep -cE {quoted})" = {want}'
    )


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--id", required=True, help="F:kebab-case-id")
    ap.add_argument("--title", required=True)
    ap.add_argument("--statement", required=True)
    ap.add_argument("--command", required=True, help="run once; both streams captured")
    ap.add_argument("--require", action="append", default=[], metavar="REGEX")
    ap.add_argument("--require-count", action="append", default=[], metavar="REGEX=N")
    ap.add_argument("--kind", default="kernel-term")
    ap.add_argument("--route", default="kernel-lean")
    ap.add_argument("--status", default="proved")
    ap.add_argument("--depends-on", action="append", default=[])
    ap.add_argument("--fragment", default="")
    ap.add_argument("--date", required=True, help="YYYY-MM-DD (no clock here on purpose)")
    ap.add_argument("--timeout", type=int, default=3600)
    ap.add_argument("--write", action="store_true", help="write the file")
    ap.add_argument(
        "--allow-population-only", action="store_true",
        help="accept a --require-count whose count no mutation moves: it catches a "
             "row disappearing but not a value changing inside a surviving row",
    )
    args = ap.parse_args(argv)

    if not args.require and not args.require_count:
        print("new-fact: give at least one --require or --require-count; a fact "
              "with no discriminating evidence is what this exists to prevent",
              file=sys.stderr)
        return 2

    print(f"running: {args.command}")
    code, text = run(args.command, args.timeout)
    print(f"  exit={code}  bytes={len(text)}")
    if code != 0:
        print("new-fact: the command failed. Every checker_command below would "
              "fail with it, so fix that first", file=sys.stderr)
        return 1

    checks: list[tuple[str, int | None]] = [(p, None) for p in args.require]
    for spec in args.require_count:
        pattern, _, count = spec.rpartition("=")
        if not pattern or not count.isdigit():
            print(f"new-fact: --require-count wants REGEX=N, got {spec!r}", file=sys.stderr)
            return 2
        checks.append((pattern, int(count)))

    problems: list[str] = []
    for pattern, want in checks:
        found = matches(pattern, text)
        issues = check_pattern(pattern, want, text, args.allow_population_only)
        verdict = "ok  " if not issues else "FAIL"
        print(f"  {verdict} matches={found:<4} {pattern}")
        problems.extend(issues)

    if problems:
        sys.stdout.flush()
        print("\nnew-fact: nothing written.", file=sys.stderr)
        for problem in problems:
            print(f"  - {problem}", file=sys.stderr)
        return 1

    fact = {
        "schema_version": 1,
        "id": args.id,
        "title": args.title,
        "statement": args.statement,
        "formal": {
            "language": "lean4",
            "statement": "TODO: the formal statement, precise enough to dispatch",
            "fragment": args.fragment or "TODO",
            "free_symbols": [],
        },
        "epistemic_status": args.status,
        "proof_route": args.route,
        "external_status": "unknown",
        "depends_on": args.depends_on,
        "axiom_footprint": [],
        "evidence": [
            {
                "id": f"{args.id.split(':', 1)[-1]}-{i}",
                "kind": args.kind,
                "supports": "TODO: what THIS row establishes that the others do not",
                "check_status": "checked",
                "checker_command": command_for(args.command, pattern, want),
                "notes": (
                    "Verified discriminating by scripts/new-fact.py: the pattern "
                    "matches the real output and fails on mutated output. TODO: say "
                    "what it is anchored on and why that anchor is the right one."
                ),
            }
            for i, (pattern, want) in enumerate(checks, start=1)
        ],
        "concept_refs": [],
        "provenance": {
            "date": args.date,
            "established_by": "TODO",
            "source": "TODO",
        },
        "notes": "TODO: WHAT THIS DOES NOT SAY.",
    }

    path = FACTS / (args.id.replace("F:", "F-") + ".json")
    body = json.dumps(fact, indent=2) + "\n"
    if not args.write:
        print(f"\n--- would write {path.relative_to(ROOT)} (pass --write) ---")
        print(body)
        return 0
    if path.exists():
        print(f"new-fact: {path.relative_to(ROOT)} already exists", file=sys.stderr)
        return 1
    path.write_text(body, encoding="utf-8")
    print(f"\nwrote {path.relative_to(ROOT)}")
    if not args.depends_on:
        print("  NOTE: no depends_on. 62 of 117 facts rest on nothing and support "
              "nothing, so proving one usually unlocks nothing — check "
              "`python3 scripts/fact-frontier.py --chains` before accepting that.")
    print("  Every TODO above is a real question; validate-facts.py will not ask them.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
