#!/usr/bin/env python3
"""Require acceptance and sign-sensitive source rejection by a Carcara binary."""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import subprocess
import sys


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checker", required=True, type=Path)
    args = parser.parse_args()
    checker = args.checker.resolve()
    root = Path(__file__).resolve().parents[1]
    fixtures = root / "crates/axeyum-solver/tests/fixtures/alethe_source_binding"
    proof = fixtures / "negative_coefficient.alethe"
    cases = [
        ("positive", fixtures / "negative_coefficient.smt2"),
        ("changed_coefficient", fixtures / "changed_positive_coefficient.smt2"),
    ]
    for name, problem in cases:
        try:
            result = subprocess.run(
                [str(checker), "check", "--allow-int-real-subtyping", str(proof), str(problem)],
                capture_output=True, text=True, timeout=30, check=False,
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            print(f"SOURCE_BINDING|{name}|ERROR|{error}", file=sys.stderr)
            return 1
        if name == "positive":
            passed = result.returncode == 0 and result.stdout.strip() == "valid"
        else:
            passed = (
                result.returncode != 0
                and result.stdout.strip() == "invalid"
                and "could not match term to any of the original problem premises" in result.stderr
            )
        print(f"SOURCE_BINDING|{name}|exit={result.returncode}|passed={int(passed)}")
        if not passed:
            print(result.stdout + result.stderr, file=sys.stderr)
            return 1
    identity = hashlib.sha256(checker.read_bytes()).hexdigest()
    print(f"SOURCE_BINDING|positive=1|negative=1|checker_sha256={identity}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
