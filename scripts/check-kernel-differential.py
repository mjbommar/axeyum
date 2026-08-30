#!/usr/bin/env python3
"""ADR-0717 S5 gate: the kernel differential (Axeyum vs. pinned Lean).

Runs `cargo test -p axeyum-lean-kernel --test kernel_differential
kernel_differential_corpus_matches_pinned_lean` with `AXEYUM_REQUIRE_LEAN=1`
(a missing pinned toolchain is a hard failure here, not a skip -- see
`crates/axeyum-lean-kernel/tests/support/lean_probe.rs`), parses its
machine-readable output, and independently re-derives the pass/fail verdict
from that output rather than trusting the test binary's own exit status
alone. This is deliberate belt-and-braces: CLAUDE.md's standing lesson is
that a checker whose exit status does not depend on what it found is worse
than no checker, so this script re-checks the same properties the Rust test
already asserts, from the OUTPUT TEXT, with its own independent guards:

  G1  the `cargo test` process itself exited 0
  G2  the corpus is non-empty (at least one `KERNEL-DIFFERENTIAL` line)
  G3  every one of the eight ADR-0717 S5 subsystems has a nonzero case count
  G4  Lean was ACTUALLY invoked (`AXEYUM-LEAN-CHECKED ... checked=N`, N > 0)
  G5  zero P0 disagreements (Axeyum accepts something Lean rejects)
  G6  zero UNEXPLAINED incompleteness (Axeyum rejects something Lean accepts,
      not registered in EXPLAINED_INCOMPLETENESS)

Any one of these failing is reported by name and the script exits 1. This
mirrors (but does not merely re-print) the corresponding assertions already
inside `kernel_differential.rs` -- see that file's `EXPLAINED_INCOMPLETENESS`
constant, which this script's own copy below must be kept in sync with.

Usage:
    scripts/check-kernel-differential.py                 # run the real gate
    scripts/check-kernel-differential.py --input FILE     # re-parse saved output
    scripts/check-kernel-differential.py --self-test       # prove G1..G6 each
                                                            # fire on the case
                                                            # that names them
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
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

# Kept in sync with `EXPLAINED_INCOMPLETENESS` in
# crates/axeyum-lean-kernel/tests/kernel_differential.rs. An entry here that
# the corpus no longer produces is harmless (G6 just never needs it); an
# entry the corpus DOES produce that is missing here fails G6, loudly.
EXPLAINED_INCOMPLETENESS = {
    "quotient::quot_sound_absent": (
        "ADR-0456 / creal.rs, int_prelude.rs, rat_prelude.rs: this kernel "
        "implements exactly Lean's Quot/Quot.mk/Quot.lift/Quot.ind and "
        "deliberately has no Quot.sound."
    ),
}

CASE_RE = re.compile(
    r"^KERNEL-DIFFERENTIAL subsystem=(?P<subsystem>\S+) name=(?P<name>\S+) "
    r"axeyum=(?P<axeyum>true|false) lean=(?P<lean>true|false) "
    r"verdict=(?P<verdict>\S+)\s*$"
)
CHECKED_RE = re.compile(r"^AXEYUM-LEAN-CHECKED kernel-differential checked=(?P<n>\d+)\s*$")


def parse_output(text: str) -> tuple[list[dict], int | None]:
    """Parse `KERNEL-DIFFERENTIAL` and `AXEYUM-LEAN-CHECKED` lines.

    Returns `(cases, checked)`. `checked` is `None` if the line never
    appeared (distinct from `0`, which the line itself cannot print --
    `report_checked` asserts `checked > 0` before printing it -- but a
    stale/adversarial input could still spell it that way, so this parser
    treats a literal `checked=0` the same as `None`: not actually checked).
    """
    cases = []
    checked = None
    for line in text.splitlines():
        m = CASE_RE.match(line.strip())
        if m:
            cases.append(m.groupdict())
            continue
        m = CHECKED_RE.match(line.strip())
        if m:
            n = int(m.group("n"))
            checked = n if n > 0 else None
    return cases, checked


def evaluate(cases: list[dict], checked: int | None, returncode: int) -> list[str]:
    """Pure gate logic: return a list of failure reasons (empty == pass).

    Deliberately independent of `parse_output`'s caller so `--self-test` can
    drive it directly with synthetic fixtures, and so a guard can be deleted
    here and re-tested without needing a real `cargo test` / `lean` run.
    """
    failures: list[str] = []

    # G2: corpus non-empty.
    if not cases:
        failures.append(
            "G2 corpus-nonempty: zero KERNEL-DIFFERENTIAL lines parsed -- "
            "the corpus is empty or the test did not run to completion"
        )

    # G3: every named subsystem has a nonzero count. (Runs even if G2 failed,
    # so a fully empty corpus names all eight, not just the umbrella G2.)
    counts: dict[str, int] = {}
    for case in cases:
        counts[case["subsystem"]] = counts.get(case["subsystem"], 0) + 1
    for subsystem in SUBSYSTEMS:
        if counts.get(subsystem, 0) == 0:
            failures.append(
                f"G3 subsystem-nonempty: subsystem `{subsystem}` has ZERO cases"
            )

    # G4: Lean was actually invoked.
    if checked is None:
        failures.append(
            "G4 lean-invoked: no AXEYUM-LEAN-CHECKED line with checked>0 -- "
            "Lean was not actually run (missing toolchain, or the suite "
            "returned before reaching the Lean loop)"
        )

    # G5: zero P0 disagreements.
    p0 = [c for c in cases if c["verdict"] == "AxeyumAcceptsLeanRejects"]
    for case in p0:
        failures.append(
            f"G5 zero-p0: {case['name']} -- Axeyum ACCEPTED something the "
            "real Lean kernel REJECTS. Potential kernel unsoundness; this "
            "preempts all other work per ADR-0717 S5."
        )

    # G6: every AxeyumRejectsLeanAccepts case is a registered, cited
    # incompleteness -- an unregistered one fails loudly rather than being
    # silently absorbed into "incompleteness happens".
    for case in cases:
        if case["verdict"] != "AxeyumRejectsLeanAccepts":
            continue
        if case["name"] not in EXPLAINED_INCOMPLETENESS:
            failures.append(
                f"G6 explained-incompleteness: {case['name']} -- Axeyum "
                "rejected something Lean accepts and this is not a "
                "registered, cited incompleteness"
            )

    # G1: the process itself must have exited 0. Checked last so the more
    # specific guards above get a chance to name the actual reason first.
    if returncode != 0:
        failures.append(f"G1 test-exit-status: cargo test exited {returncode}")

    return failures


def run_real_gate(repo_root: Path) -> int:
    env = dict(os.environ)
    env["AXEYUM_REQUIRE_LEAN"] = "1"
    cmd = [
        "cargo",
        "test",
        "-p",
        "axeyum-lean-kernel",
        "--test",
        "kernel_differential",
        "kernel_differential_corpus_matches_pinned_lean",
        "--",
        "--nocapture",
        "--test-threads=1",
    ]
    proc = subprocess.run(
        cmd,
        cwd=repo_root,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    output = proc.stdout + proc.stderr
    sys.stdout.write(output)
    return finish(output, proc.returncode)


def run_from_file(path: Path) -> int:
    text = path.read_text()
    return finish(text, 0 if "test result: ok" in text else 1)


def finish(output: str, returncode: int) -> int:
    cases, checked = parse_output(output)
    failures = evaluate(cases, checked, returncode)

    counts: dict[str, int] = {}
    for case in cases:
        counts[case["subsystem"]] = counts.get(case["subsystem"], 0) + 1
    print("KERNEL-DIFFERENTIAL per-subsystem counts:")
    for subsystem in SUBSYSTEMS:
        print(f"  {subsystem}: {counts.get(subsystem, 0)}")
    print(f"KERNEL-DIFFERENTIAL total cases: {len(cases)}")
    print(f"KERNEL-DIFFERENTIAL lean checked: {checked}")
    explained = [
        c["name"] for c in cases if c["verdict"] == "AxeyumRejectsLeanAccepts"
    ]
    if explained:
        print(f"KERNEL-DIFFERENTIAL explained incompleteness: {explained}")

    if failures:
        print("KERNEL-DIFFERENTIAL GATE FAILED:", file=sys.stderr)
        for reason in failures:
            print(f"  - {reason}", file=sys.stderr)
        return 1
    print("KERNEL-DIFFERENTIAL GATE PASSED")
    return 0


def self_test() -> int:
    """Prove each guard fires on exactly the input shape that names it, and
    that an all-clear input passes with zero failures. This is the
    fail-on-absence proof the roadmap requires: run with an EMPTY corpus and
    confirm the gate exits naming the reason, plus one fixture per guard.
    """
    ok_case = lambda subsystem, name: {
        "subsystem": subsystem,
        "name": name,
        "axeyum": "true",
        "lean": "true",
        "verdict": "AgreeAccept",
    }

    def full_corpus(extra: dict | None = None) -> list[dict]:
        cases = [ok_case(s, f"{s}::positive_a") for s in SUBSYSTEMS]
        cases += [
            {
                "subsystem": s,
                "name": f"{s}::negative_a",
                "axeyum": "false",
                "lean": "false",
                "verdict": "AgreeReject",
            }
            for s in SUBSYSTEMS
        ]
        if extra:
            cases.append(extra)
        return cases

    failed = False

    def check(label: str, cases: list[dict], checked: int | None, rc: int, expect_guard: str | None):
        nonlocal failed
        failures = evaluate(cases, checked, rc)
        if expect_guard is None:
            if failures:
                print(f"SELF-TEST FAIL [{label}]: expected PASS, got {failures}")
                failed = True
            else:
                print(f"SELF-TEST ok [{label}]: passes as expected")
            return
        if not any(f.startswith(expect_guard) for f in failures):
            print(
                f"SELF-TEST FAIL [{label}]: expected a {expect_guard} failure, "
                f"got {failures}"
            )
            failed = True
        else:
            print(f"SELF-TEST ok [{label}]: {expect_guard} fired as expected")

    # All-clear: full corpus, Lean checked, exit 0 -> PASS.
    check("all-clear", full_corpus(), 32, 0, None)

    # G2: totally empty corpus (the mandatory "prove it" case).
    check("empty-corpus", [], None, 0, "G2")

    # G3: one subsystem entirely missing.
    partial = [c for c in full_corpus() if c["subsystem"] != "quotient"]
    check("missing-subsystem", partial, 16, 0, "G3")

    # G4: cases present but Lean was never actually invoked.
    check("lean-not-invoked", full_corpus(), None, 0, "G4")

    # G5: a P0 disagreement.
    p0_extra = {
        "subsystem": "conversion",
        "name": "conversion::adversarial",
        "axeyum": "true",
        "lean": "false",
        "verdict": "AxeyumAcceptsLeanRejects",
    }
    check("p0-disagreement", full_corpus(p0_extra), 33, 0, "G5")

    # G6: an unexplained incompleteness (not in EXPLAINED_INCOMPLETENESS).
    unexplained_extra = {
        "subsystem": "conversion",
        "name": "conversion::surprise_gap",
        "axeyum": "false",
        "lean": "true",
        "verdict": "AxeyumRejectsLeanAccepts",
    }
    check("unexplained-incompleteness", full_corpus(unexplained_extra), 33, 0, "G6")

    # A REGISTERED incompleteness must NOT fail G6.
    registered_extra = {
        "subsystem": "quotient",
        "name": "quotient::quot_sound_absent",
        "axeyum": "false",
        "lean": "true",
        "verdict": "AxeyumRejectsLeanAccepts",
    }
    check("registered-incompleteness-is-not-a-failure", full_corpus(registered_extra), 33, 0, None)

    # G1: nonzero exit status alone, everything else clean.
    check("nonzero-exit", full_corpus(), 32, 1, "G1")

    if failed:
        print("SELF-TEST: at least one case did not behave as expected")
        return 1
    print("SELF-TEST: all guards fire on their own case; all-clear input passes")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--input",
        type=Path,
        help="re-parse a saved cargo-test output file instead of running it",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="prove each guard fires on exactly the input that names it (no cargo/lean run)",
    )
    args = parser.parse_args()

    if args.self_test:
        return self_test()
    if args.input:
        return run_from_file(args.input)

    repo_root = Path(__file__).resolve().parent.parent
    return run_real_gate(repo_root)


if __name__ == "__main__":
    sys.exit(main())
