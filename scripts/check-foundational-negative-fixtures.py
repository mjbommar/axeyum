#!/usr/bin/env python3
"""Assert that committed foundational-resource negative fixtures are rejected."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
VALIDATOR = ROOT / "scripts" / "validate-foundational-example-pack.py"
FIXTURE_ROOT = ROOT / "artifacts" / "fixtures" / "foundational-example-pack-invalid"

CASES = [
    (
        "unknown-field",
        "metadata.field_ids references unknown fields: imaginary_field",
    ),
    (
        "expected-results-mismatch",
        "metadata.expected_results must match expected.checks ids",
    ),
    (
        "unknown-witness-reference",
        "uses-missing-witness references unknown witness missing-witness",
    ),
]


class NegativeFixtureError(Exception):
    pass


def fail(message: str) -> None:
    raise NegativeFixtureError(message)


def run_case(case_id: str, expected_error: str) -> None:
    fixture = FIXTURE_ROOT / case_id
    if not fixture.is_dir():
        fail(f"missing negative fixture directory: {fixture.relative_to(ROOT)}")
    result = subprocess.run(
        [sys.executable, str(VALIDATOR), str(fixture.relative_to(ROOT))],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if result.returncode == 0:
        fail(f"{case_id} unexpectedly passed validation")
    if expected_error not in result.stderr:
        fail(
            f"{case_id} failed with the wrong diagnostic; expected substring "
            f"{expected_error!r}, got {result.stderr.strip()!r}"
        )


def main() -> int:
    for case_id, expected_error in CASES:
        run_case(case_id, expected_error)
    print(f"validated {len(CASES)} foundational example-pack negative fixture(s)")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except NegativeFixtureError as error:
        print(f"check-foundational-negative-fixtures: {error}", file=sys.stderr)
        raise SystemExit(1)
