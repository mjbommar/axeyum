"""Mutation controls: each guard in `run-controls.sh` must be killed by a
mutation of the thing it names, and by nothing else.

A checker that cannot fail is worse than no checker.  Six of seven guards in
one suite in this repository turned out to be removable with everything still
green, because they all rejected through one shared check.  This script is the
measurement that says these do not.

Run:  python3 mutants.py     (copies to a scratch root; never mutates in place)
"""

import pathlib
import shutil
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
LANE = HERE.parent

# (name, file, [(old, new), ...], guards expected to die)
MUTANTS = [
    (
        "census: rank every row, ignoring the ADR-1936/1941 partition",
        "census-summarize.py",
        [
            (
                '            if r.get("open_after", "na") != "na":\n'
                "                unclassified.append(r)",
                "            if False:\n                unclassified.append(r)",
            )
        ],
        # Three guards: dropping the partition changes the counts, lets the
        # row whose budget vanished into an open segment be ranked by its
        # give-up reason (the one thing ADR-1936 exists to forbid), and
        # collapses the two ADR-1941 readings into one.
        [
            "the ADR-1936/1941 partition is wrong",
            "an UNCLASSIFIED row was ranked",
            "the two ADR-1941 readings were not both published",
        ],
    ),
    (
        "census: ADR-1941 reverted -- classify by attempts= alone",
        "census-summarize.py",
        [
            (
                '            if r.get("open_after", "na") != "na":\n'
                "                unclassified.append(r)",
                "            if int(a) < ladder:\n                unclassified.append(r)",
            )
        ],
        # This is the PRE-ADR-1941 behaviour, and it must not pass silently.
        # It wrongly buries the short-ladder row, which on the real QF_UFBV
        # census is 77 of 87 rows and a 53-file single-constant finding.
        # Three guards: the counts move, the short-ladder row stops being
        # ranked, and the two readings collapse into one (with the attempts=
        # rule restored, strict_unclassified == len(unclassified)), which is
        # exactly the state ADR-1941 step 6 exists to make visible.
        [
            "the ADR-1936/1941 partition is wrong",
            "a row with a SHORT ladder and no open segment was not ranked",
            "the two ADR-1941 readings were not both published",
        ],
    ),
    (
        "census: publish only ONE of the two ADR-1941 readings",
        "census-summarize.py",
        [
            (
                '            f" {strict_unclassified} rows UNCLASSIFIED;"',
                '            f" {len(unclassified)} rows UNCLASSIFIED;"',
            )
        ],
        ["the two ADR-1941 readings were not both published"],
    ),
    (
        "board: the disagreement check compares nothing",
        "summarize.py",
        [
            ('                if r["status"] != v:', "                if False:"),
            ('                    if r[s] != v:', "                    if False:"),
        ],
        ["the disagreement check did not fire"],
    ),
    (
        "board: every row counts as decided",
        "summarize.py",
        [('DECIDED = {"sat", "unsat"}', 'DECIDED = {"sat", "unsat", "unknown"}')],
        # Two guards, deliberately: widening DECIDED empties the winnable set AND
        # makes `unknown` comparable against `sat`, so the disagreement check now
        # has a row it should have flagged and does not reach.  A cascade that
        # names two different defects is the opposite of guards sharing one check.
        ["the winnable set was miscounted", "the disagreement check did not fire"],
    ),
    (
        "census: internal errors are silently dropped",
        "census-summarize.py",
        [
            (
                '        err = [r for r in rs if r["giveup"].startswith("give-up kind=Error")]',
                "        err = []",
            )
        ],
        # Two guards: with no error rows there is neither a count line nor a
        # repro path to find.
        [
            "the internal-error row was not reported",
            "reported without a repro path",
        ],
    ),
    (
        "census: the internal error is reported WITHOUT a repro path",
        "census-summarize.py",
        [
            (
                '                        print(f"            repro: {r[\'file\']}")',
                '                        print("            repro: (elided)")',
            )
        ],
        ["reported without a repro path"],
    ),
    (
        "census: an internal error is RANKED as a capability blocker",
        "census-summarize.py",
        [
            (
                '        errors = [r for r in classified'
                ' if r["giveup"].startswith("give-up kind=Error")]',
                "        errors = []",
            )
        ],
        ["the ADR-1936/1941 partition is wrong"],
    ),
    (
        "census: a missing census renders as an empty one",
        "census-summarize.py",
        [
            (
                '        if rs is None:\n            print(f"== {div}: census DID NOT RUN")\n            continue',
                "        if rs is None:\n            rs = []\n        if not rs:\n            continue",
            )
        ],
        ["a missing census renders the same as an empty one"],
    ),
]


def main():
    base = subprocess.run(
        ["bash", str(HERE / "run-controls.sh")], capture_output=True, text=True
    )
    if base.returncode != 0:
        print("ABORT: the UNMUTATED suite is already failing:")
        print(base.stdout)
        return 2
    print("baseline: CONTROLS-OK")

    bad = 0
    for name, fname, edits, expect in MUTANTS:
        with tempfile.TemporaryDirectory() as td:
            root = pathlib.Path(td) / "lane"
            shutil.copytree(LANE, root)
            p = root / fname
            src = p.read_text()
            for old, new in edits:
                if old not in src:
                    print(f"  !! {name}: ANCHOR MISSED in {fname} -- mutant not applied")
                    bad += 1
                    src = None
                    break
                src = src.replace(old, new)
            if src is None:
                continue
            p.write_text(src)
            r = subprocess.run(
                ["bash", str(root / "controls" / "run-controls.sh")],
                capture_output=True,
                text=True,
            )
            died = [e for e in expect if e in r.stdout]
            extra = [
                ln
                for ln in r.stdout.splitlines()
                if ln.startswith("FAIL:") and not any(e in ln for e in expect)
            ]
            ok = r.returncode != 0 and len(died) == len(expect) and not extra
            print(f"  {'kill ' if ok else '!!   '} {name}")
            if not ok:
                bad += 1
                print(f"       rc={r.returncode} expected={expect}")
                print(f"       got: {r.stdout.strip()}")
    print("MUTANTS-OK" if bad == 0 else f"MUTANTS-FAILED ({bad})")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
