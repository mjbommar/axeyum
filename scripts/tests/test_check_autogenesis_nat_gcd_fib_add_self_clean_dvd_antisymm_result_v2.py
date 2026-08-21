from __future__ import annotations

import pathlib
import subprocess


ROOT = pathlib.Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-clean-dvd-antisymm-result-v2.py"


def test_retained_v2_decline_passes() -> None:
    result = subprocess.run(["python3", str(CHECKER)], cwd=ROOT, check=False)
    assert result.returncode == 0


def test_checker_is_bound_to_manifest_digest() -> None:
    source = CHECKER.read_text()
    assert "EXPECTED_MANIFEST_SHA256" in source
    assert "sha256(MANIFEST) == EXPECTED_MANIFEST_SHA256" in source


def test_checker_requires_zero_authority() -> None:
    source = CHECKER.read_text()
    assert '\"target_credit\": 0' in source
    assert '\"ledger_writes\": 0' in source
    assert 'execution[\"composition_operations\"] == 0' in source
