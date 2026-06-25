#!/usr/bin/env python3
"""Regenerate the App-B property SCOREBOARD by re-running the consumer-bench binary.

This is a thin, deterministic wrapper around `axeyum-consumer-bench` (App D): it
runs the construction-known bounded-property corpus through the `axeyum-property`
SDK and rewrites `docs/consumer-track/property/SCOREBOARD.md`. The Rust binary is
the single source of truth (it also asserts the DISAGREE = 0 soundness floor and
panics otherwise); this script just invokes it from the workspace root so the
scoreboard is regenerable with one command.

Usage:
    scripts/gen-property-scoreboard.py            # regenerate the committed file
    scripts/gen-property-scoreboard.py --check     # verify it is up to date (CI)
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SCOREBOARD = REPO_ROOT / "docs" / "consumer-track" / "property" / "SCOREBOARD.md"


def main() -> int:
    check = "--check" in sys.argv[1:]
    cmd = ["cargo", "run", "--quiet", "-p", "axeyum-consumer-bench", "--"]
    if check:
        cmd += ["--check", str(SCOREBOARD)]
    else:
        cmd += [str(SCOREBOARD)]

    # Build caps mirror the project gate (-j4); the binary enforces DISAGREE = 0.
    env_jobs = {"CARGO_BUILD_JOBS": "4"}
    proc = subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        env={**__import__("os").environ, **env_jobs},
        check=False,
    )
    if proc.returncode != 0:
        action = "stale" if check else "failed"
        print(f"scoreboard generation {action} (exit {proc.returncode})", file=sys.stderr)
        return proc.returncode
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
