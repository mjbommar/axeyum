#!/usr/bin/env python3
"""ADR-0717 S5 ratchet over artifacts/kernel-differential/mutant-kill-table.json.

Full kernel-source mutation testing (mutate crates/axeyum-lean-kernel/src,
rebuild, rerun against pinned Lean, revert) needs ~8 kernel rebuilds and
mutates tracked source in place -- exactly the operation CLAUDE.md's shared-
worktree section forbids running unattended or in CI (it breaks OTHER
lanes' concurrent builds for however long the mutant is on disk). So it is
a human-triggered, by-hand re-measurement, not a script this gate re-runs.

What this script DOES check, cheaply and every run: that the artifact
recording the last measurement is INTERNALLY CONSISTENT and covers every
ADR-0717 S5 subsystem -- so a lane cannot silently delete an inconvenient
entry, claim a KILLED without naming what it killed, or let the artifact
drift out of the shape the roadmap's "ratchet on killed critical mutants"
exit criterion expects. This is the ratchet; the measurement itself is
`docs/plan/status/390-l0-s5-kernel-differential.md`'s recorded procedure.

Guards, named the same way as check-kernel-differential.py's:
  M1  the artifact file exists and parses as JSON
  M2  every ADR-0717 S5 subsystem has exactly one mutant entry
  M3  every mutant's status is KILLED or SURVIVED (no silent third state)
  M4  every KILLED mutant names a kill signal AND (a flipped case OR an
      explicit non-attributable note) -- a KILLED with neither is a claim
      with no evidence
  M5  the killed/survived counts in `summary` match the entries themselves
  M6  at least one mutant per subsystem is present in EITHER killed_subsystems
      or survived_subsystems (no subsystem silently omitted from the summary)

Usage:
    scripts/check-kernel-differential-mutants.py
    scripts/check-kernel-differential-mutants.py --self-test
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

SUBSYSTEMS = [
    "conversion",
    "universes",
    "inductives",
    "recursors",
    "projections",
    "literals",
    "quotient",
    "proof_irrelevance",
]

DEFAULT_ARTIFACT = Path("artifacts/kernel-differential/mutant-kill-table.json")


def evaluate(data: dict) -> list[str]:
    """Pure guard logic over an already-parsed artifact dict."""
    failures: list[str] = []

    mutants = data.get("mutants")
    if not isinstance(mutants, list) or not mutants:
        failures.append("M2 subsystem-coverage: `mutants` is missing or empty")
        mutants = []

    by_subsystem: dict[str, list[dict]] = {}
    for entry in mutants:
        subsystem = entry.get("subsystem")
        by_subsystem.setdefault(subsystem, []).append(entry)

    for subsystem in SUBSYSTEMS:
        n = len(by_subsystem.get(subsystem, []))
        if n != 1:
            failures.append(
                f"M2 subsystem-coverage: subsystem `{subsystem}` has {n} mutant "
                "entries, expected exactly 1"
            )

    for entry in mutants:
        name = entry.get("subsystem", "<unknown>")
        status = entry.get("status")
        if status not in ("KILLED", "SURVIVED"):
            failures.append(
                f"M3 status-shape: subsystem `{name}` has status "
                f"{status!r}, expected KILLED or SURVIVED"
            )
            continue
        if status == "KILLED":
            has_signal = bool(entry.get("kill_signal"))
            has_cases = bool(entry.get("flipped_cases"))
            has_note = bool(entry.get("note"))
            if not has_signal:
                failures.append(
                    f"M4 killed-has-evidence: subsystem `{name}` is KILLED but "
                    "names no kill_signal"
                )
            if not (has_cases or has_note):
                failures.append(
                    f"M4 killed-has-evidence: subsystem `{name}` is KILLED but "
                    "names neither a flipped case nor an explanatory note"
                )

    summary = data.get("summary", {})
    killed_entries = {e["subsystem"] for e in mutants if e.get("status") == "KILLED"}
    survived_entries = {e["subsystem"] for e in mutants if e.get("status") == "SURVIVED"}
    summary_killed = set(summary.get("killed_subsystems", []))
    summary_survived = set(summary.get("survived_subsystems", []))

    if killed_entries != summary_killed:
        failures.append(
            f"M5 summary-matches-entries: killed_subsystems {sorted(summary_killed)} "
            f"!= entries actually marked KILLED {sorted(killed_entries)}"
        )
    if survived_entries != summary_survived:
        failures.append(
            f"M5 summary-matches-entries: survived_subsystems {sorted(summary_survived)} "
            f"!= entries actually marked SURVIVED {sorted(survived_entries)}"
        )
    if summary.get("killed") != len(killed_entries):
        failures.append(
            f"M5 summary-matches-entries: summary.killed={summary.get('killed')} "
            f"!= counted {len(killed_entries)}"
        )
    if summary.get("survived") != len(survived_entries):
        failures.append(
            f"M5 summary-matches-entries: summary.survived={summary.get('survived')} "
            f"!= counted {len(survived_entries)}"
        )

    for subsystem in SUBSYSTEMS:
        if subsystem not in summary_killed and subsystem not in summary_survived:
            failures.append(
                f"M6 no-omitted-subsystem: `{subsystem}` is in neither "
                "killed_subsystems nor survived_subsystems in `summary`"
            )

    return failures


def run(artifact_path: Path) -> int:
    if not artifact_path.exists():
        print(f"KERNEL-DIFFERENTIAL-MUTANTS GATE FAILED:", file=sys.stderr)
        print(f"  - M1 artifact-exists: {artifact_path} does not exist", file=sys.stderr)
        return 1
    try:
        data = json.loads(artifact_path.read_text())
    except json.JSONDecodeError as exc:
        print("KERNEL-DIFFERENTIAL-MUTANTS GATE FAILED:", file=sys.stderr)
        print(f"  - M1 artifact-parses: {artifact_path} is not valid JSON: {exc}", file=sys.stderr)
        return 1

    failures = evaluate(data)
    if failures:
        print("KERNEL-DIFFERENTIAL-MUTANTS GATE FAILED:", file=sys.stderr)
        for reason in failures:
            print(f"  - {reason}", file=sys.stderr)
        return 1

    print(
        f"KERNEL-DIFFERENTIAL-MUTANTS GATE PASSED: {len(data['mutants'])} mutants, "
        f"{data['summary']['killed']} killed / {data['summary']['survived']} survived, "
        f"all {len(SUBSYSTEMS)} subsystems covered"
    )
    return 0


def self_test() -> int:
    good = {
        "mutants": [
            {"subsystem": s, "status": "KILLED", "kill_signal": "P0", "flipped_cases": [f"{s}::x"]}
            for s in SUBSYSTEMS
        ],
        "summary": {
            "killed": len(SUBSYSTEMS),
            "survived": 0,
            "killed_subsystems": SUBSYSTEMS,
            "survived_subsystems": [],
        },
    }
    ok = 0
    total = 0

    def expect(label, data, want_guard):
        nonlocal ok, total
        total += 1
        failures = evaluate(data)
        if want_guard is None:
            if not failures:
                print(f"ok [{label}]: passes as expected")
                ok += 1
            else:
                print(f"FAIL [{label}]: expected pass, got {failures}")
            return
        if any(f.startswith(want_guard) for f in failures):
            print(f"ok [{label}]: {want_guard} fired as expected")
            ok += 1
        else:
            print(f"FAIL [{label}]: expected {want_guard}, got {failures}")

    import copy

    expect("all-clear", good, None)

    missing_subsystem = copy.deepcopy(good)
    missing_subsystem["mutants"] = [m for m in missing_subsystem["mutants"] if m["subsystem"] != "quotient"]
    expect("missing-subsystem", missing_subsystem, "M2")

    bad_status = copy.deepcopy(good)
    bad_status["mutants"][0]["status"] = "UNKNOWN"
    expect("bad-status", bad_status, "M3")

    no_evidence = copy.deepcopy(good)
    no_evidence["mutants"][0]["kill_signal"] = None
    no_evidence["mutants"][0]["flipped_cases"] = []
    expect("killed-no-evidence", no_evidence, "M4")

    wrong_summary = copy.deepcopy(good)
    wrong_summary["summary"]["killed"] = 3
    expect("wrong-summary-count", wrong_summary, "M5")

    omitted = copy.deepcopy(good)
    omitted["summary"]["killed_subsystems"] = [s for s in SUBSYSTEMS if s != "conversion"]
    omitted["summary"]["killed"] = len(SUBSYSTEMS) - 1
    expect("omitted-from-summary", omitted, "M5")

    if ok != total:
        print(f"SELF-TEST: {ok}/{total} passed")
        return 1
    print(f"SELF-TEST: {ok}/{total} passed")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact", type=Path, default=DEFAULT_ARTIFACT)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    return run(args.artifact)


if __name__ == "__main__":
    sys.exit(main())
