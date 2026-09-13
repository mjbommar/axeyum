#!/usr/bin/env python3
"""Mutation control for the ADR-1966 guards.

Deletes ONE guard at a time from a SCRATCH copy of the tree (never the shared
worktree) and runs the suite, so the table says which guards are individually
load-bearing.  A guard that no test kills is reported as such rather than
shipped as a safety margin -- ADR-1927 deleted one on exactly that finding.
"""

import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path("/data0/axeyum/scratch/snap-dispatch-decline-audit-df5030319")
AUTO = ROOT / "crates/axeyum-solver/src/auto.rs"
ORIG = AUTO.read_text()

# Each mutation REMOVES one guard by restoring the pre-fix propagation.
MUTATIONS = {
    "uf-nra/check_with_nra": (
        """    let result = match crate::nra::check_with_nra(arena, &eliminated, &nra_config) {
        Ok(result) => result,
        Err(SolverError::Unsupported(message)) => {
            with_recorder(rec, |t| {
                t.record_declined("uf-nra", unsupported_decline(&message));
            });
            return Ok(None);
        }
        Err(other) => return Err(other),
    };""",
        """    let result = crate::nra::check_with_nra(arena, &eliminated, &nra_config)?;""",
    ),
    "uf-arithmetic/array-valued": (
        """        let eager = match crate::check_with_uf_arithmetic(arena, assertions, &eager_config) {
            Ok(result) => result,
            Err(SolverError::Unsupported(message)) => CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Incomplete,
                detail: format!("eager UF+arithmetic route declined: {message}"),
            }),
            Err(other) => return Err(other),
        };
        match eager {""",
        """        match crate::check_with_uf_arithmetic(arena, assertions, &eager_config)? {""",
    ),
    "rung_or_decline (helper)": (
        """        Err(SolverError::Unsupported(message)) => {
            with_recorder(rec, |t| {
                t.record_declined(route, unsupported_decline(&message));
            });
            Ok(None)
        }
        other => other,""",
        """        other => other,""",
    ),
}

# Consecutive guards on ONE path are not separable by a verdict-level test:
# whichever fires first stops the dispatch before the later one is reachable,
# so the earlier guard strictly dominates. `uf-arithmetic` and the
# `uf-routes` wrapper are such a pair. The combined mutant is what decides
# whether the PAIR is load-bearing.
COMBINED = {
    "uf-arithmetic + rung_or_decline (both)": [
        "uf-arithmetic/array-valued",
        "rung_or_decline (helper)",
    ],
}

SUITES = ["dispatch_rung_refusal_declines", "quant_ladder_rung_refusal_declines"]


def run_suites() -> dict[str, set[str]]:
    dead: dict[str, set[str]] = {}
    for suite in SUITES:
        out = subprocess.run(
            [
                "cargo", "test", "-p", "axeyum-solver", "--features", "full",
                "--test", suite, "--", "--test-threads=1",
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
            env={**__import__("os").environ,
                 "CARGO_TARGET_DIR": "/data0/axeyum/dispatch-decline-audit-mut-target"},
        )
        text = out.stdout + out.stderr
        if "running " not in text:
            print(f"  !! {suite}: suite did not run\n{text[-2000:]}")
            dead[suite] = {"<did-not-compile-or-run>"}
            continue
        n = re.search(r"running (\d+) tests", text)
        if not n or n.group(1) == "0":
            dead[suite] = {"<zero tests -- inert>"}
            continue
        dead[suite] = set(re.findall(r"^test (\S+) \.\.\. FAILED", text, re.M))
    return dead


def main() -> int:
    print("=== BASELINE (all guards present) ===")
    AUTO.write_text(ORIG)
    base = run_suites()
    for s, d in base.items():
        print(f"  {s}: failing = {sorted(d) or 'none'}")
    if any(d for d in base.values()):
        print("ABORT: the unmutated tree is not green; every row below would be noise")
        return 1

    rows = []
    for name, (present, removed) in MUTATIONS.items():
        if ORIG.count(present) != 1:
            print(f"  !! {name}: anchor matched {ORIG.count(present)} times -- NOT 1. "
                  f"MISSING SUBJECT, not a surviving mutant.")
            rows.append((name, {"<anchor did not match>"}))
            continue
        AUTO.write_text(ORIG.replace(present, removed))
        print(f"=== MUTANT: {name} deleted ===")
        d = run_suites()
        killed = {f"{s}::{t}" for s, ts in d.items() for t in ts}
        print(f"  tests that died: {sorted(killed) or 'NONE'}")
        rows.append((name, killed))

    for name, members in COMBINED.items():
        text = ORIG
        ok = True
        for m in members:
            present, removed = MUTATIONS[m]
            if text.count(present) != 1:
                print(f"  !! {name}: anchor for {m} matched {text.count(present)} times")
                ok = False
                break
            text = text.replace(present, removed)
        if not ok:
            rows.append((name, {"<anchor did not match>"}))
            continue
        AUTO.write_text(text)
        print(f"=== MUTANT: {name} deleted ===")
        d = run_suites()
        killed = {f"{s}::{t}" for s, ts in d.items() for t in ts}
        print(f"  tests that died: {sorted(killed) or 'NONE'}")
        rows.append((name, killed))

    AUTO.write_text(ORIG)

    print("\n=== TABLE ===")
    for name, killed in rows:
        print(f"{name:<28} deaths={len(killed):<2} {sorted(killed)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
