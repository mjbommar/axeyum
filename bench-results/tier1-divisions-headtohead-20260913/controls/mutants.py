"""Mutation controls: each guard in `run-controls.sh` must be killed by a
mutation of the thing it names, and by nothing else.

A checker that cannot fail is worse than no checker.  Six of seven guards in
one suite in this repository turned out to be removable with everything still
green, because they all rejected through one shared check.  `CONTROLS-OK` on a
first run is not evidence that the guards work; this script is.

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
        # FOUR guards, each naming a different defect.  Note the third: with
        # the partition gone the internal-error row reaches the ranked list
        # too, so this mutation is caught by a guard about a different ADR.
        # Guards that share one check would have died as a single message.
        [
            "the ADR-1936/1941 partition is wrong",
            "an UNCLASSIFIED row was ranked",
            "an internal-error row was RANKED as a capability blocker",
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
        # The PRE-ADR-1941 behaviour: it buries the short-ladder row and
        # collapses the two readings into one.  The internal-error SECTION
        # survives, because `err` is derived from all rows rather than from the
        # classified bucket -- which is the right design and is why those two
        # guards are absent here rather than merely unlisted.
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
        "census: ADR-1950 reverted -- drop the ms_left line entirely",
        "census-summarize.py",
        [
            (
                '            print(f"           {lt}")',
                "            pass",
            )
        ],
        # Both halves of the ADR-1950 pair go dark together: without the line,
        # a ROUND row and a CLOCK row are indistinguishable in the output,
        # which is precisely the merge the ADR forbids.
        [
            "a ROUND row was not shown with its unspent budget",
            "a CLOCK row was not shown as clock-bound",
        ],
    ),
    (
        "census: ADR-1950 -- call every budget row clock-bound",
        "census-summarize.py",
        [
            (
                'note = ("clock NOT binding" if med > BUDGET_MS * 0.5\n'
                '                        else "clock-bound" if med < BUDGET_MS * 0.05 else "mixed")',
                'note = "clock-bound"',
            )
        ],
        # Only the ROUND guard dies: the CLOCK row is genuinely clock-bound, so
        # its guard still passes.  A mutation that killed BOTH would mean the
        # two guards share one check, which is the thing being ruled out.
        ["a ROUND row was not shown with its unspent budget"],
    ),
    (
        "census: a front-door PARSE refusal is buried as an internal error",
        "census-summarize.py",
        [
            (
                '    return g.startswith("give-up kind=Error") and "parse error" not in g',
                '    return g.startswith("give-up kind=Error")',
            )
        ],
        # This is the board-six behaviour, and on THESE divisions it would hide
        # the lane's headline finding: the nested-array refusal would be listed
        # as a bug rather than ranked as a capability gap.
        # FOUR guards.  Two are the point of the mutation; the other two fire
        # because the error section now holds TWO rows instead of one, which is
        # the visible symptom of a capability gap being filed as a bug.
        [
            "the ADR-1936/1941 partition is wrong",
            "a front-door PARSE refusal was not ranked as a capability gap",
            "the internal-error row was not reported",
            "reported without a repro path",
        ],
    ),
    (
        "census: internal errors are silently dropped",
        "census-summarize.py",
        [
            (
                '        err = [r for r in rs if is_internal_error(r["giveup"])]',
                "        err = []",
            )
        ],
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
                '        errors = [r for r in classified if is_internal_error(r["giveup"])]\n'
                '        classified = [r for r in classified if not is_internal_error(r["giveup"])]',
                "        errors = []",
            )
        ],
        [
            "the ADR-1936/1941 partition is wrong",
            "an internal-error row was RANKED as a capability blocker",
        ],
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
        # A cascade naming FOUR different defects: the winnable set empties,
        # `unknown` becomes comparable against `sat` so the disagreement check
        # no longer reaches its row, the probe rate becomes 100 % everywhere,
        # and the vacuous fixture acquires comparable verdicts so its zero stops
        # being labelled.  Four guards, four different messages -- which is the
        # evidence that they do not reject through one shared check.
        [
            "the winnable set was miscounted",
            "the disagreement check did not fire",
            "a board AT the probe rate was not CONFIRMED",
            "a zero over ZERO comparable verdicts was printed as a result",
        ],
    ),
    (
        "board: a zero over zero comparable verdicts is printed as a result",
        "summarize.py",
        [
            (
                '        vac = "  <-- VACUOUS: nothing checked any verdict we produced" if (\n'
                "            not ncomp and not dis) else \"\"",
                '        vac = ""',
            )
        ],
        ["a zero over ZERO comparable verdicts was printed as a result"],
    ),
    (
        "board: EVERY board is labelled vacuous",
        "summarize.py",
        [
            (
                "        vac = \"  <-- VACUOUS: nothing checked any verdict we produced\" if (\n"
                "            not ncomp and not dis) else \"\"",
                '        vac = "  <-- VACUOUS: nothing checked any verdict we produced"',
            )
        ],
        # The inverted half.  A label applied to everything is worth as little
        # as one applied to nothing, and only this mutant distinguishes them.
        ["a board with comparable verdicts was labelled VACUOUS"],
    ),
    (
        "board: the probe verdict is hardcoded to CONFIRMED",
        "summarize.py",
        [
            (
                'verdict = "CONFIRMED" if lo <= rate <= hi else "REFUTED"',
                'verdict = "CONFIRMED"',
            )
        ],
        ["a board far outside the probe interval was not REFUTED"],
    ),
    (
        "board: the probe verdict is hardcoded to REFUTED",
        "summarize.py",
        [
            (
                'verdict = "CONFIRMED" if lo <= rate <= hi else "REFUTED"',
                'verdict = "REFUTED"',
            )
        ],
        ["a board AT the probe rate was not CONFIRMED"],
    ),
    (
        "board: the k=0 interval collapses to a point (normal approximation)",
        "summarize.py",
        [
            (
                "    p = k / n\n"
                "    d = 1 + z * z / n\n"
                "    c = p + z * z / (2 * n)\n"
                "    r = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n))\n"
                "    return ((c - r) / d, (c + r) / d)",
                "    p = k / n\n"
                "    r = z * math.sqrt(p * (1 - p) / n)\n"
                "    return (max(0.0, p - r), p + r)",
            )
        ],
        # With the normal interval ALIA's 0/24 becomes the single point 0.0, so
        # every possible board 'refutes' it -- a verdict manufactured by the
        # statistic rather than measured.  The degeneracy guard is what catches
        # it; the REFUTED guard does not, because ALIA still reads REFUTED.
        ["the k=0 interval is degenerate"],
    ),
    (
        "crossdiv: the nested-array family is folded into OTHER",
        "census-crossdiv.py",
        [
            (
                '    ("nested array element sort refused (PARSE)", "PARSE",\n'
                '     lambda g: "nested array element sort is unsupported" in g),',
                "",
            )
        ],
        [
            "the crossdiv table lost the nested-array family",
            "the nested-array SHARE table is wrong",
        ],
    ),
    (
        "crossdiv: the nested-array SHARE uses the census size, not the winnable set",
        "census-crossdiv.py",
        [
            (
                '        w = len([x for x in wf.read_text().split("\\n") if x]) if wf.exists() else 0',
                "        w = 6 if wf.exists() else 0",
            )
        ],
        ["the nested-array SHARE table is wrong"],
    ),
    (
        "crossdiv: an internal error is counted as a capability kind",
        "census-crossdiv.py",
        [
            (
                '    ("terminal internal error (NOT a capability gap)", "INTERNAL",\n'
                '     lambda g: g.startswith("give-up kind=Error")),',
                "",
            )
        ],
        ["an internal error was not separated from the capability kinds"],
    ),
    (
        "crossdiv: the OTHER bucket is not printed",
        "census-crossdiv.py",
        [
            (
                '    print("\\n== OTHER bucket, in full (a catch-all must not hide a family) ==")',
                "    pass",
            )
        ],
        ["the OTHER bucket is not printed"],
    ),
    (
        "crossdiv: a missing census renders as an empty one",
        "census-crossdiv.py",
        [("    if missing:", "    if False:")],
        ["six missing censuses rendered as six empty ones"],
    ),
    (
        "loadframe: the OVERLAP detector can only print ok",
        "loadframe.sh",
        [("        *,5,*|*,13,*|*,6,*|*,14,*) ov=OVERLAP ;;", "        *) ov=ok ;;")],
        # Checked by the OTHER suite in this directory, which extracts the
        # classifier from loadframe.sh rather than re-typing it -- so this
        # mutation changes what that suite runs and the MUST-fire specs fail.
        ["__loadframe__"],
    ),
]


def run_suite(root):
    return subprocess.run(
        ["bash", str(root / "controls" / "run-controls.sh")],
        capture_output=True,
        text=True,
    )


def run_loadframe_control(root):
    return subprocess.run(
        ["bash", str(root / "controls" / "loadframe-overlap-control.sh")],
        capture_output=True,
        text=True,
    )


def main():
    base = run_suite(LANE)
    if base.returncode != 0:
        print("ABORT: the UNMUTATED suite is already failing:")
        print(base.stdout)
        return 2
    lbase = run_loadframe_control(LANE)
    if lbase.returncode != 0:
        print("ABORT: the UNMUTATED loadframe control is already failing:")
        print(lbase.stdout)
        return 2
    print("baseline: CONTROLS-OK + LOADFRAME-OVERLAP-OK")

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

            if expect == ["__loadframe__"]:
                r = run_loadframe_control(root)
                ok = r.returncode != 0 and "FAIL: spec" in r.stdout
                print(f"  {'kill ' if ok else '!!   '} {name}")
                if not ok:
                    bad += 1
                    print(f"       rc={r.returncode} got: {r.stdout.strip()}")
                continue

            r = run_suite(root)
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
