#!/usr/bin/env python3
"""Mutation control for the interface-policy guards.

Each mutation puts back a behaviour the tests exist to forbid, asserts its own
anchor applied first (so a green run cannot come from a mutation that never
landed), runs the module's tests, and restores the file whatever happens.

Run from the lane's worktree root. It edits ONE file and restores it in a
`finally`, so nothing is ever committed in a mutated state.

A mutation that kills ZERO tests is the finding, not the failure of the script:
the first run of this battery found that making the care filter unreachable
killed nothing, because every existing test either called `care_graph_pairs`
directly or used a proposal the filter could not shrink. The test that closes
that gap (`the_care_filter_is_actually_applied_by_the_policy`) was written from
this battery's output.
"""

import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
TARGET = ROOT / "crates/axeyum-solver/src/uflia_interface.rs"

MUTATIONS = [
    (
        "the policy never consults the care graph",
        "        matches!(self, Self::CareGraph | Self::CareGraphTruncate)",
        "        false",
    ),
    (
        "truncation never fires (care-truncate declines like care)",
        "        matches!(self, Self::CareGraphTruncate)",
        "        false",
    ),
    (
        "a cap decline is not recorded",
        "                c.pair_cap_declines = c.pair_cap_declines.saturating_add(1);",
        "                c.pair_cap_declines = c.pair_cap_declines;",
    ),
    (
        "the care graph ignores the argument POSITION (all-pairs within a group)",
        "                for (&a, &b) in tuples[i].iter().zip(tuples[j].iter()) {",
        "                for (&a, &b) in tuples[i].iter().zip(tuples[j].iter().rev()) {",
    ),
]


def run_tests():
    out = subprocess.run(
        [
            str(ROOT / "scripts/cargo-serialized.sh"),
            "test",
            "-p",
            "axeyum-solver",
            "--lib",
            "--features",
            "full",
            "uflia_interface",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    text = out.stdout + out.stderr
    if "error[" in text or "error: could not compile" in text:
        return None, text
    failed = re.findall(r"^test (\S+) \.\.\. FAILED$", text, re.M)
    counts = re.search(r"test result: \w+\. (\d+) passed; (\d+) failed", text)
    return (failed, counts.groups() if counts else None), text


def main():
    baseline, text = run_tests()
    if baseline is None or baseline[0]:
        print("UNMUTATED TREE IS NOT GREEN — a mutation battery on a red tree says nothing")
        print(text[-1200:])
        return 1
    print(f"unmutated: {baseline[1][0]} passed, 0 failed")

    ok = True
    for name, old, new in MUTATIONS:
        original = TARGET.read_text()
        if original.count(old) != 1:
            print(f"SKIPPED (anchor occurs {original.count(old)}x): {name}")
            ok = False
            continue
        try:
            TARGET.write_text(original.replace(old, new, 1))
            assert TARGET.read_text() != original, "mutation did not apply"
            result, text = run_tests()
            if result is None:
                print(f"{name}: DID NOT COMPILE (a compile error is not a killed test)")
                ok = False
                continue
            failed, counts = result
            verdict = "KILLED" if failed else "SURVIVED — nothing pins this"
            print(f"{name}: {verdict} {failed} (counts {counts})")
            if not failed:
                ok = False
        finally:
            TARGET.write_text(original)
    print("MUTATION_BATTERY", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
