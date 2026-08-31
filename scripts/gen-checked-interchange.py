#!/usr/bin/env python3
"""Regenerate `artifacts/checked-interchange/census/*.census.json` (L4 phase
C2). NOT part of `just check` / `scripts/check.sh` -- those run only
`scripts/check-checked-interchange.py`, which validates the committed
artifact and needs no Lean toolchain and no cargo build, matching
`check-declaration-graph.py`/`check-graph-join.py`'s own gen/check split.

This script's whole job is to run the real pipeline
(`crates/axeyum-lean-import/tests/checked_interchange_credited_roots.rs`),
which does the actual export / fresh-reimport / pinned-Lean-replay work and
writes the census artifact itself. This wrapper exists only so a human or CI
job has one command, with `AXEYUM_REQUIRE_LEAN=1` forced -- C2's exit
criterion (`missing=0` is mandatory) cannot be honestly satisfied by a suite
that quietly skipped because no Lean toolchain was found, so this refuses to
run in a mode that could produce that silently-vacuous census.

Usage:
    python3 scripts/gen-checked-interchange.py
    python3 scripts/gen-checked-interchange.py --check   # regenerate, then
                                                          # run the validator
"""
from __future__ import annotations

import argparse
import os
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="after regenerating, also run scripts/check-checked-interchange.py",
    )
    args = parser.parse_args()

    wrapper = REPO_ROOT / "scripts" / "cargo-serialized.sh"
    if not wrapper.is_file():
        print(f"missing {wrapper}", file=sys.stderr)
        return 2

    env = dict(os.environ)
    env["AXEYUM_REQUIRE_LEAN"] = "1"

    cmd = [
        str(wrapper),
        "test",
        "--release",
        "-p",
        "axeyum-lean-import",
        "--test",
        "checked_interchange_credited_roots",
        "--",
        "--test-threads=1",
    ]
    print(f"running: {' '.join(cmd)}")
    result = subprocess.run(cmd, cwd=REPO_ROOT, env=env)
    if result.returncode != 0:
        print(
            f"checked-interchange regeneration FAILED (exit {result.returncode}) -- "
            "the census artifact was not (re)written by a clean run",
            file=sys.stderr,
        )
        return result.returncode

    census_path = (
        REPO_ROOT
        / "artifacts"
        / "checked-interchange"
        / "census"
        / "credited-roots-v1.census.json"
    )
    if not census_path.is_file():
        print(
            f"the pipeline exited 0 but did not write {census_path} -- treat this "
            "as a failure, not a pass over nothing",
            file=sys.stderr,
        )
        return 1
    print(f"wrote {census_path}")

    if args.check:
        checker = REPO_ROOT / "scripts" / "check-checked-interchange.py"
        result = subprocess.run([sys.executable, str(checker)], cwd=REPO_ROOT)
        return result.returncode

    return 0


if __name__ == "__main__":
    sys.exit(main())
