#!/usr/bin/env python3
"""Pre-merge gate for L3 phase D1 (declarative declaration spec, ADR-0965).

Runs, in order, and fails on the first thing that does not hold:

  1. Builds `examples/declaration_spec_pilot` in release (debug SIGABRTs on
     kernel stack depth -- see this crate's CLAUDE.md).
  2. `--dump-names` a full real kernel name inventory (the Int prelude,
     which is a superset of the Nat prelude and includes
     `Nat.inverseIndex`) to `artifacts/declaration-spec/generated/
     kernel-names-snapshot.txt`, and requires a NONZERO name count.
  3. Runs `gen-declaration-spec.py --check` over the pilot spec against that
     snapshot and requires PASS.
  4. Runs `gen-declaration-spec.py` over each of the three adversarial
     negative fixtures INDIVIDUALLY and requires each one to FAIL with the
     specific guard tag it exists to exercise -- a fixture that passes, or
     fails for the WRONG reason, fails this gate.
  5. Runs the pilot binary's default mode and requires exit 0 and the
     `verdict=DIGESTS_IDENTICAL` marker, with a nonzero declarations/
     equations count parsed from its own output (fail on absence: an empty
     comparison or a skipped equation set is a failure here, not a pass).
  6. Runs `gen-declaration-spec.py` (writing) over the pilot spec and
     confirms the generated artifacts are unchanged from what is committed
     (freshness, same pattern as `gen-plan.py --check`).

Every step prints a `DECLARATION_SPEC_CHECK|step=...|verdict=...` line so a
failure is attributable to a specific step without re-reading this file.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SPECS_DIR = REPO_ROOT / "artifacts" / "declaration-spec"
GENERATED_DIR = SPECS_DIR / "generated"
SNAPSHOT = GENERATED_DIR / "kernel-names-snapshot.txt"
PILOT_SPEC = SPECS_DIR / "nat-squarefree.json"
FIXTURES_DIR = SPECS_DIR / "negative-fixtures"
GEN_SCRIPT = REPO_ROOT / "scripts" / "gen-declaration-spec.py"
EXAMPLE_BIN = REPO_ROOT / "target" / "release" / "examples" / "declaration_spec_pilot"

# (fixture file, required guard tag)
NEGATIVE_FIXTURES = [
    ("dup-name-cross-prelude.json", "GUARD:CROSS_PRELUDE_DUPLICATE"),
    ("dup-name-in-corpus.json", "GUARD:DUPLICATE_NAME"),
    ("missing-phase.json", "GUARD:MISSING_PHASE"),
    ("dependency-cycle.json", "GUARD:DEPENDENCY_CYCLE"),
    ("dep-mismatch.json", "GUARD:DEP_MISMATCH"),
]


def report(step: str, verdict: str, detail: str = "") -> None:
    suffix = f"|{detail}" if detail else ""
    print(f"DECLARATION_SPEC_CHECK|step={step}|verdict={verdict}{suffix}")


def fail(step: str, detail: str) -> int:
    report(step, "FAIL", detail)
    return 1


def run(cmd: list[str], **kwargs) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, capture_output=True, text=True, cwd=REPO_ROOT, **kwargs)


def main() -> int:
    # 1. Build the pilot example (release -- see module docstring).
    cargo_bin = "cargo"
    build = run([cargo_bin, "build", "--release", "-p", "axeyum-lean-kernel", "--example", "declaration_spec_pilot"])
    if build.returncode != 0:
        sys.stderr.write(build.stdout + build.stderr)
        return fail("build", f"cargo build exited {build.returncode}")
    report("build", "PASS")

    if not EXAMPLE_BIN.exists():
        return fail("build", f"expected binary missing: {EXAMPLE_BIN}")

    # 2. Dump the real kernel name inventory.
    GENERATED_DIR.mkdir(parents=True, exist_ok=True)
    dump = run([str(EXAMPLE_BIN), "--dump-names"])
    if dump.returncode != 0:
        return fail("dump-names", f"exited {dump.returncode}: {dump.stderr.strip()}")
    names = [line for line in dump.stdout.splitlines() if line.strip()]
    if not names:
        return fail("dump-names", "GUARD:EMPTY_SNAPSHOT zero names dumped")
    SNAPSHOT.write_text("\n".join(names) + "\n", encoding="utf-8")
    m = re.search(r"names=(\d+)", dump.stderr)
    report("dump-names", "PASS", f"names={len(names)}" + (f" (self-reported {m.group(1)})" if m else ""))

    # 3. Validate the pilot spec against the real snapshot.
    pilot_check = run([sys.executable, str(GEN_SCRIPT), "--check", "--only", str(PILOT_SPEC), "--snapshot", str(SNAPSHOT)])
    if pilot_check.returncode != 0:
        sys.stderr.write(pilot_check.stdout + pilot_check.stderr)
        return fail("pilot-spec-validation", "gen-declaration-spec.py --check did not PASS")
    if "verdict=PASS" not in pilot_check.stdout:
        return fail("pilot-spec-validation", "no verdict=PASS in generator output")
    report("pilot-spec-validation", "PASS")

    # 4. Each negative fixture must fail, and fail for its OWN guard.
    for fixture_name, required_guard in NEGATIVE_FIXTURES:
        fixture_path = FIXTURES_DIR / fixture_name
        result = run(
            [sys.executable, str(GEN_SCRIPT), "--check", "--only", str(fixture_path), "--snapshot", str(SNAPSHOT)]
        )
        combined = result.stdout + result.stderr
        if result.returncode == 0:
            return fail(f"negative-fixture:{fixture_name}", "fixture PASSED validation -- guard did not fire")
        if required_guard not in combined:
            return fail(
                f"negative-fixture:{fixture_name}",
                f"failed, but not with the expected guard {required_guard!r}: {combined.strip()!r}",
            )
        report(f"negative-fixture:{fixture_name}", "PASS", f"refused via {required_guard}")

    # 5. Run the pilot binary itself and require the digest-identical marker.
    pilot_run = run([str(EXAMPLE_BIN)])
    if pilot_run.returncode != 0:
        sys.stderr.write(pilot_run.stdout + pilot_run.stderr)
        return fail("pilot-run", f"exited {pilot_run.returncode}")
    if "verdict=DIGESTS_IDENTICAL" not in pilot_run.stdout:
        sys.stderr.write(pilot_run.stdout)
        return fail("pilot-run", "no verdict=DIGESTS_IDENTICAL in output")
    decl_m = re.search(r"declarations_checked=(\d+)", pilot_run.stdout)
    eq_m = re.search(r"equations_checked=(\d+)", pilot_run.stdout)
    decl_n = int(decl_m.group(1)) if decl_m else 0
    eq_n = int(eq_m.group(1)) if eq_m else 0
    if decl_n == 0:
        return fail("pilot-run", "GUARD:EMPTY_CORPUS zero declarations checked")
    if eq_n == 0:
        return fail("pilot-run", "GUARD:EMPTY_CORPUS zero equations checked")
    report("pilot-run", "PASS", f"declarations_checked={decl_n}|equations_checked={eq_n}")

    # 6. Freshness: regenerate and confirm the committed generated artifacts
    # did not drift (same pattern as gen-plan.py --check).
    gen = run([sys.executable, str(GEN_SCRIPT), "--only", str(PILOT_SPEC), "--snapshot", str(SNAPSHOT)])
    if gen.returncode != 0:
        sys.stderr.write(gen.stdout + gen.stderr)
        return fail("generated-freshness", "generation itself failed")
    diff = run(["git", "diff", "--stat", "--", str(GENERATED_DIR)])
    if diff.stdout.strip():
        return fail("generated-freshness", f"generated artifacts drifted:\n{diff.stdout}")
    report("generated-freshness", "PASS")

    report("all", "PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
