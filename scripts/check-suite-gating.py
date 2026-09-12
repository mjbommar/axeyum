#!/usr/bin/env python3
"""Every integration suite is GATED or EXPLICITLY EXCUSED — never silently neither.

Why this exists (2026-09-12): `unknown_reason_coverage` went red on `main` and
stayed red across three lane merges while a full pre-push battery passed GREEN
over it, because `hooks/pre-push` named 18 of 327 integration suites and that
one was not among them. Nothing was broken; nothing was watching.

A hand-maintained list of suites cannot notice a suite nobody added to it. So
this derives the population from the filesystem — the authority — and requires
every member to be either named by the hook or listed in the excuse file with a
reason. A new suite that is neither FAILS here, which is the whole point.

The 309 pre-existing ungated suites are seeded as `unreviewed:` so the debt is
COUNTED rather than hidden. Reducing that count is real work; this gate only
guarantees it cannot silently grow.

Exit status depends on the finding. `--print-ungated` lists the backlog.
"""

import os
import re
import sys
import glob

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TESTS = os.path.join(ROOT, "crates", "axeyum-solver", "tests")
HOOK = os.path.join(ROOT, "hooks", "pre-push")
EXCUSES = os.path.join(ROOT, "scripts", "suite-gating-excuses.txt")


def suites():
    return {os.path.basename(p)[:-3] for p in glob.glob(os.path.join(TESTS, "*.rs"))}


def gated(hook_text, names):
    """A suite is gated if the hook names it as a whole word.

    Deliberately generous: a false POSITIVE here weakens the gate, so the
    control suite pins that a suite the hook does not mention is reported
    ungated.
    """
    return {n for n in names if re.search(r"\b" + re.escape(n) + r"\b", hook_text)}


def excused():
    out = {}
    if not os.path.exists(EXCUSES):
        return out
    for line in open(EXCUSES):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        name, _, reason = line.partition(":")
        out[name.strip()] = reason.strip()
    return out


def main() -> int:
    names = suites()
    if not names:
        print("SUITE_GATING|FAIL|found zero integration suites — wrong path?")
        return 1
    hook_text = open(HOOK).read()
    g = gated(hook_text, names)
    e = excused()
    missing = sorted(names - g - set(e))
    unreviewed = sorted(n for n, r in e.items() if r.startswith("unreviewed"))
    stale = sorted(set(e) - names)

    if "--print-ungated" in sys.argv:
        for n in unreviewed:
            print(n)
        return 0

    ok = True
    if missing:
        ok = False
        print(f"SUITE_GATING|FAIL|{len(missing)} suite(s) neither gated nor excused:")
        for n in missing:
            print(f"    {n}")
        print("  Add it to hooks/pre-push, or to scripts/suite-gating-excuses.txt")
        print("  with a reason. 'Nobody got round to it' is a reason; silence is not.")
    if stale:
        ok = False
        print(f"SUITE_GATING|FAIL|{len(stale)} excuse(s) name a suite that no longer exists:")
        for n in stale:
            print(f"    {n}")

    print(
        f"SUITE_GATING|suites={len(names)}|gated={len(g)}|excused={len(e)}"
        f"|unreviewed_backlog={len(unreviewed)}|{'PASS' if ok else 'FAIL'}"
    )
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
