#!/usr/bin/env python3
"""Run every `scripts/tests/test_*.py` control that no gate names by hand.

WHY THIS EXISTS
---------------
`scripts/check-control-registration.sh` measured, on 2026-08-27, that **188 of
382** Python control suites were named by no caller -- not `scripts/check.sh`,
not the `justfile`, not `hooks/pre-push`, not a workflow. They pass when run by
hand and they never run. The gate pinned that count as a numeric floor, so the
floor was permanent and nobody had chosen it; it was whatever the number
happened to be the day the ratchet was written.

That is the repository's own audited defect one level out: *a check that cannot
fail and a check that never runs are the same green.*

The fix is the same move `scripts/check-shape-duplicates.py` makes for duplicate
declarations and `scripts/check-absence-claims.py` makes for absence claims:
**derive the set from the authority (the filesystem), and make every exclusion a
written decision** instead of an anonymous number.

WHAT IT RUNS
------------
    discovered  =  scripts/tests/test_*.py
    named       =  suites a caller already invokes by name
    opted out   =  scripts/control-optout.tsv, one reason per line
    RUN HERE    =  discovered - named - opted out

Suites a caller already names are deliberately NOT re-run here: they are covered,
and running them twice doubles the aggregate gate's cost for no extra coverage.
So this script is the *catch-all*, and its contents shrink automatically as
individual steps are added. Nothing has to be moved between lists by hand.

TEETH
-----
Three ways this fails, each of which the old numeric floor could not detect:

  * any suite fails               -> exit 1, naming it
  * any suite runs ZERO tests     -> exit 1. This is the repository's oldest
    trap (`running 0 tests ... ok`) and it is live here: 10 of the 188 orphans
    were written in the *pytest* dialect -- bare `def test_x()` functions with
    no `unittest.TestCase` -- which `python3 -m unittest` collects as nothing.
    Registering one of those without this guard would add a step that cannot
    fail.
  * the corpus is implausibly small -> exit 2. A glob that stops matching would
    otherwise make this whole gate pass vacuously, which is the failure it
    exists to prevent.

Usage:
    scripts/run-python-controls.py                # run them (the gate form)
    scripts/run-python-controls.py --list         # what it would run
    scripts/run-python-controls.py --list-named   # covered by a named step
    scripts/run-python-controls.py --list-optout  # excluded, with reasons
    AXEYUM_CONTROL_JOBS=4 scripts/run-python-controls.py
"""

from __future__ import annotations

import argparse
import concurrent.futures as cf
import os
import pathlib
import re
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]
TESTS = ROOT / "scripts" / "tests"
OPTOUT = ROOT / "scripts" / "control-optout.tsv"

# Where a control may be claimed from by name. Identical to the list in
# `scripts/check-control-registration.sh`; that gate independently re-greps for
# THIS script, so the two do not both have to be right about the same thing.
CALLERS = ("scripts/check.sh", "justfile", "hooks/pre-push", ".github/workflows")

# Corpus floors. A glob that matches nothing exits 0 in every naive
# implementation of this script, so these are not decoration.
MIN_DISCOVERED = 200
MIN_TESTS = 200


class ControlError(Exception):
    """A structural problem with the control corpus itself."""


def caller_text() -> str:
    """Concatenated caller sources with whole-line comments stripped.

    COMMENTS ARE NOT CALLERS -- the day the registration gate landed, a
    `# Control: scripts/tests/...` line in `hooks/pre-push` satisfied a plain
    `grep -F` and a control nothing ran reported as registered.
    """
    parts: list[str] = []
    for name in CALLERS:
        p = ROOT / name
        if not p.exists():
            continue
        if p.is_dir():
            for f in sorted(p.iterdir()):
                if f.is_file():
                    parts.append(f.read_text(errors="replace"))
        else:
            parts.append(re.sub(r"(?m)^[ \t]*#.*$", "", p.read_text(errors="replace")))
    return "".join(parts)


def discovered() -> list[str]:
    return sorted(f.stem for f in TESTS.glob("test_*.py"))


def hyphenated_py() -> list[str]:
    """`.py` controls whose names contain a hyphen.

    Unreachable by `python3 -m unittest scripts.tests.X` (not an importable
    module name) AND invisible to the `test_*.py` glob, so such a file is inert
    twice over. Confirmed by probe on 2026-08-27. Reported, never run.
    """
    return sorted(f.name for f in TESTS.glob("*.py") if "-" in f.name)


def read_optout() -> dict[str, str]:
    """Parse `scripts/control-optout.tsv` into {suite: reason}.

    Format is `name<TAB>reason`; `#` comment lines and blanks are skipped. A
    missing reason is an ERROR, not an empty string: the entire point of this
    file is that every exclusion is a written decision, and an entry with no
    reason is the anonymous numeric floor again with extra steps.
    """
    out: dict[str, str] = {}
    if not OPTOUT.exists():
        raise ControlError(f"{OPTOUT} is missing; the opt-out list is the gate's authority")
    for lineno, raw in enumerate(OPTOUT.read_text().splitlines(), 1):
        line = raw.rstrip("\n")
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        if "\t" not in line:
            raise ControlError(f"{OPTOUT}:{lineno}: no TAB -- every entry needs `name<TAB>reason`")
        name, reason = line.split("\t", 1)
        name, reason = name.strip(), reason.strip()
        if not name:
            raise ControlError(f"{OPTOUT}:{lineno}: empty suite name")
        if not reason:
            raise ControlError(f"{OPTOUT}:{lineno}: {name} has no reason")
        if name in out:
            raise ControlError(f"{OPTOUT}:{lineno}: {name} is listed twice")
        out[name] = reason
    return out


def named_suites(text: str, names: list[str]) -> set[str]:
    """Suites a caller invokes by name, in either invocation form.

    BOTH forms count. A suite run as `python3 scripts/tests/x.py` is as run as
    one named `python3 -m unittest scripts.tests.x`; counting only the module
    form overcounted orphans by 18 when this logic first landed in the shell
    gate.
    """
    return {n for n in names if f"scripts.tests.{n}" in text or f"scripts/tests/{n}.py" in text}


def partition() -> tuple[list[str], set[str], dict[str, str], list[str]]:
    names = discovered()
    if len(names) < MIN_DISCOVERED:
        raise ControlError(
            f"found only {len(names)} suite(s) under {TESTS}; the glob is looking at "
            f"the wrong place and an empty corpus would make this gate pass vacuously"
        )
    optout = read_optout()
    stale = sorted(set(optout) - set(names))
    named = named_suites(caller_text(), names)
    mine = [n for n in names if n not in named and n not in optout]
    return mine, named, optout, stale


def run_one(name: str, timeout: int) -> dict:
    t0 = time.time()
    try:
        p = subprocess.run(
            [sys.executable, "-B", "-m", "unittest", f"scripts.tests.{name}"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        rc, out = p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired as exc:
        rc = "TIMEOUT"
        out = (exc.stdout or b"").decode(errors="replace") if exc.stdout else ""
    m = re.search(r"^Ran (\d+) test", out, re.M)
    return {
        "name": name,
        "rc": rc,
        "tests": int(m.group(1)) if m else 0,
        "secs": round(time.time() - t0, 1),
        "tail": "\n".join(out.strip().splitlines()[-8:]),
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--list", action="store_true", help="print the suites this would run")
    ap.add_argument("--list-named", action="store_true", help="print suites a named step covers")
    ap.add_argument("--list-optout", action="store_true", help="print excluded suites and reasons")
    ap.add_argument("--timeout", type=int, default=300, help="per-suite timeout, seconds")
    args = ap.parse_args()

    try:
        mine, named, optout, stale = partition()
    except ControlError as exc:
        print(f"PYTHON_CONTROLS_ERROR|{exc}", file=sys.stderr)
        return 2

    if stale:
        # Fails in the OTHER direction: an allowlist that only ever grows is a
        # place for dead entries to hide.
        for s in stale:
            print(
                f"PYTHON_CONTROLS_ERROR|{OPTOUT} lists `{s}`, which no longer exists. "
                f"Delete the line -- a stale exclusion hides nothing and misstates the corpus.",
                file=sys.stderr,
            )
        return 2

    if args.list:
        for n in mine:
            print(n)
        return 0
    if args.list_named:
        for n in sorted(named):
            print(n)
        return 0
    if args.list_optout:
        for n, reason in sorted(optout.items()):
            print(f"{n}\t{reason}")
        return 0

    jobs = int(os.environ.get("AXEYUM_CONTROL_JOBS", "0")) or min(8, (os.cpu_count() or 4))
    t0 = time.time()
    with cf.ThreadPoolExecutor(max_workers=jobs) as ex:
        results = list(ex.map(lambda n: run_one(n, args.timeout), mine))

    # A suite that COLLECTED NOTHING is reported as such and not as a generic
    # failure, whatever its exit code. Python >= 3.12 exits 5 for "no tests ran"
    # and older interpreters exit 0 with `Ran 0 tests ... OK`; the first reads as
    # an ordinary failure and the second as a pass, and neither names the actual
    # problem. The condition is `tests == 0`, not an exit code, so it holds on
    # both.
    vacuous = [r for r in results if r["tests"] == 0]
    vacuous_names = {r["name"] for r in vacuous}
    failed = [r for r in results if r["rc"] != 0 and r["name"] not in vacuous_names]
    total_tests = sum(r["tests"] for r in results)

    print(
        f"PYTHON_CONTROLS|suites={len(mine)}|tests={total_tests}|failed={len(failed)}"
        f"|vacuous={len(vacuous)}|named_elsewhere={len(named)}|optout={len(optout)}"
        f"|jobs={jobs}|wall={round(time.time() - t0, 1)}s"
    )

    for r in failed:
        print(f"PYTHON_CONTROLS_ERROR|{r['name']} FAILED (rc={r['rc']}, {r['secs']}s)", file=sys.stderr)
        print("  " + r["tail"].replace("\n", "\n  "), file=sys.stderr)
    for r in vacuous:
        print(
            f"PYTHON_CONTROLS_ERROR|{r['name']} ran ZERO tests (rc={r['rc']}). "
            f"`python3 -m unittest` collects `unittest.TestCase` methods only, so a "
            f"pytest-dialect suite (bare `def test_x()`) is a step that cannot fail.",
            file=sys.stderr,
        )

    # A run whose corpus collapsed is not a pass. Both floors are independent:
    # the suite count can hold while every suite silently collects nothing.
    if total_tests < MIN_TESTS:
        print(
            f"PYTHON_CONTROLS_ERROR|only {total_tests} test(s) ran across {len(mine)} "
            f"suite(s), below the floor of {MIN_TESTS}. Something is collecting nothing.",
            file=sys.stderr,
        )
        return 2

    if failed or vacuous:
        return 1
    print(f"  {len(mine)} catch-all control suite(s), {total_tests} tests, all green")
    return 0


if __name__ == "__main__":
    sys.exit(main())
