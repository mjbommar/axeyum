#!/usr/bin/env python3
"""Gate: the bounded proof-plan IR (L3 phase D5,
docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md).

D5 asks for a small inspectable proof-plan representation compiled to
ordinary kernel terms -- never taught to the kernel -- with a deterministic
compiler, plans that render for review, malformed plans that decline, and at
least three existing proof families that become shorter without changing
theorem identities or footprints.

The IR and compiler live in `crates/axeyum-lean-kernel/src/proof_plan.rs`.
Unlike the D1 declaration-spec pilot (a Python-generated spec plus a Rust
interpreter), D5 needed no code generation: a `Plan` value is built directly
in the Rust `declare_*` functions that use it, so there is no
`gen-proof-plan.py` counterpart here -- deliberately, see this crate's module
doc for the reasoning. This script is the CHECK half only.

Three guards, run in order so the cheapest failure surfaces first:

  UNIT_TESTS_NONZERO   `cargo test -p axeyum-lean-kernel --lib proof_plan::`
                       exits 0 AND reports a NONZERO passed count -- the
                       standing "confirm a nonzero test count" rule; a
                       feature-gate or filter typo that silently runs zero
                       tests must fail this gate, not pass it.
  DIGEST_PROBE_RUNS    `examples/proof_plan_digest_probe` exits 0 and prints
                       exactly six rows (one per theorem whose proof was
                       rewritten to go through `proof_plan`).
  FOOTPRINT_UNCHANGED  every one of those six rows carries axiom_footprint
                       length 0 -- the Nat prelude is axiom-free, and a
                       rewritten proof that pulled in an axiom would be a
                       regression this gate must catch, not a detail the
                       digest float past.

# Asking for evidence and finding none is a FAILURE

An empty digest-probe output (zero rows) is not "nothing to check" -- it
means the probe did not build or the six theorems it names are gone, and
this script exits 1 rather than treating that as vacuously fine.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

EXPECTED_SUBJECTS = [
    "dvd_add_iff_left",
    "dvd_mod_iff_gen",
    "dvd_iff_mod_eq_zero",
    "dvd_gcd_mul_iff_dvd_mul",
    "dvd_mul_gcd_iff_dvd_mul",
    "dvd_gcd_mul_gcd_iff_dvd_mul",
]

PASSED_RE = re.compile(r"test result: ok\. (\d+) passed; (\d+) failed")


def run(cmd: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd, cwd=REPO_ROOT, capture_output=True, text=True, check=False
    )


def check_unit_tests() -> bool:
    proc = run(
        [
            "cargo",
            "test",
            "-p",
            "axeyum-lean-kernel",
            "--lib",
            "proof_plan::",
        ]
    )
    combined = proc.stdout + proc.stderr
    if proc.returncode != 0:
        print("FAIL UNIT_TESTS_NONZERO: cargo test exited nonzero")
        print(combined[-4000:])
        return False
    m = PASSED_RE.search(combined)
    if not m:
        print("FAIL UNIT_TESTS_NONZERO: could not find a 'test result:' line")
        print(combined[-2000:])
        return False
    passed, failed = int(m.group(1)), int(m.group(2))
    if failed != 0:
        print(f"FAIL UNIT_TESTS_NONZERO: {failed} test(s) failed")
        return False
    if passed == 0:
        print(
            "FAIL UNIT_TESTS_NONZERO: 0 tests ran -- a filter or feature gate "
            "made this suite vacuous"
        )
        return False
    print(f"PASS UNIT_TESTS_NONZERO: {passed} passed, 0 failed")
    return True


def check_digest_probe() -> tuple[bool, list[tuple[str, int, str]]]:
    proc = run(
        [
            "cargo",
            "run",
            "--release",
            "-p",
            "axeyum-lean-kernel",
            "--example",
            "proof_plan_digest_probe",
        ]
    )
    if proc.returncode != 0:
        print("FAIL DIGEST_PROBE_RUNS: example exited nonzero")
        print(proc.stdout[-2000:])
        print(proc.stderr[-2000:])
        return False, []

    rows: list[tuple[str, int, str]] = []
    for line in proc.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        parts = line.split("\t")
        if len(parts) != 3:
            continue
        name, footprint_len, digest = parts
        try:
            rows.append((name, int(footprint_len), digest))
        except ValueError:
            continue

    if len(rows) != len(EXPECTED_SUBJECTS):
        print(
            f"FAIL DIGEST_PROBE_RUNS: expected {len(EXPECTED_SUBJECTS)} rows, "
            f"got {len(rows)}"
        )
        return False, rows

    seen = {name for name, _, _ in rows}
    missing = set(EXPECTED_SUBJECTS) - seen
    if missing:
        print(f"FAIL DIGEST_PROBE_RUNS: missing subjects {sorted(missing)}")
        return False, rows

    print(f"PASS DIGEST_PROBE_RUNS: {len(rows)} rows, all expected subjects present")
    return True, rows


def check_footprint_unchanged(rows: list[tuple[str, int, str]]) -> bool:
    bad = [(name, fp) for name, fp, _ in rows if fp != 0]
    if bad:
        print(f"FAIL FOOTPRINT_UNCHANGED: nonzero footprint at {bad}")
        return False
    print(f"PASS FOOTPRINT_UNCHANGED: all {len(rows)} rows carry footprint 0")
    return True


def main() -> int:
    ok = True
    ok &= check_unit_tests()
    digest_ok, rows = check_digest_probe()
    ok &= digest_ok
    if digest_ok:
        ok &= check_footprint_unchanged(rows)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
