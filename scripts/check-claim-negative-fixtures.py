#!/usr/bin/env python3
"""Assert the claim gates reject the committed invalid fixtures.

A green gate over an empty set is not evidence; a validator that has never
rejected anything is untested. Each fixture under
artifacts/fixtures/claims-invalid/<name>/ must make its gate exit nonzero AND
emit the expected diagnostic substring.

Two gates are exercised: validate-claims.py (structure, refs, epistemic
discipline) and check-claim-certificates.py (semantic re-derivation). The
cube-cover fixtures target the latter — a decomposed refutation is only
evidence if the cover is exhaustive, uniformly passing, and licensed by the
formula's own case-split clauses, so each of those three failure modes has a
fixture that must be caught.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FIXTURES = ROOT / "artifacts" / "fixtures" / "claims-invalid"
VALIDATOR = ROOT / "scripts" / "validate-claims.py"
CERT_CHECKER = ROOT / "scripts" / "check-claim-certificates.py"

EXPECTED = {
    "computed-without-checked-evidence":
        "requires at least one evidence row with check_status 'checked'",
    "bound-citation-checked":
        "bound-citation 'cite' must be not-checked",
    "sha-mismatch":
        "sha256 mismatch",
    "regenerable-without-toolchain":
        "no provenance.toolchain is pinned",
    # A recorded command that cannot be run is not a re-check recipe. This is
    # the `certify_cover` defect: green for months on the two rows carrying
    # the headline upper bounds.
    "checker-command-not-runnable":
        "neither a known interpreter nor a path",
}

# fixtures whose defect is semantic, caught by the certificate checker
EXPECTED_CERT = {
    "cube-cover-not-exhaustive": "cover is NOT exhaustive",
    "cube-cover-failed-check": "proof check FAILED",
    "cube-cover-unlicensed-branch": "the case split is not",
    # An ADAPTIVE cover is a tree, so its completeness obligation is "the
    # cubes are exactly the leaf set of a complete branch trie" rather than
    # "the cubes are exactly the product". Both ways of breaking that -- a
    # subtree nothing covers, and a cube recorded alongside its own children --
    # get a fixture, because a tree cover that is not a partition proves
    # nothing while looking exactly like one that does.
    "cube-tree-cover-incomplete": "cover is NOT complete",
    "cube-tree-cover-overlapping": "overlaps itself",
}


def run_fixture(name: str, needle: str, gate: Path, extra: list[str]) -> bool:
    """True on success: the gate rejected the fixture with the right message."""
    root = FIXTURES / name
    if not root.is_dir():
        print(f"FAIL {name}: fixture directory missing")
        return False
    r = subprocess.run(
        [sys.executable, str(gate), "--root", str(root), *extra],
        capture_output=True, text=True)
    combined = r.stderr + r.stdout
    if r.returncode == 0:
        print(f"FAIL {name}: {gate.name} accepted an invalid claim")
        return False
    if needle not in combined:
        print(f"FAIL {name}: rejected, but without the expected diagnostic "
              f"{needle!r}\noutput: {combined[-400:]}")
        return False
    print(f"OK   {name}: rejected with expected diagnostic")
    return True


def main() -> int:
    failures = 0
    for name, needle in sorted(EXPECTED.items()):
        if not run_fixture(name, needle, VALIDATOR, ["--quiet"]):
            failures += 1
    for name, needle in sorted(EXPECTED_CERT.items()):
        if not run_fixture(name, needle, CERT_CHECKER, []):
            failures += 1
    total = len(EXPECTED) + len(EXPECTED_CERT)
    print(f"\n{total} fixtures, {failures} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
