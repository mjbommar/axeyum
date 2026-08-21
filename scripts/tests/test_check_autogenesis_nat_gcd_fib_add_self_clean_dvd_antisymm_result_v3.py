from __future__ import annotations

import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-clean-dvd-antisymm-result-v3.py"


def test_v3_decline_passes() -> None:
    assert subprocess.run(["python3", str(CHECKER)], cwd=ROOT, check=False).returncode == 0


def test_checker_binds_the_missing_leaf_and_zero_authority() -> None:
    source = CHECKER.read_text()
    assert "Nat.succ_pos" in source
    assert "all(value == 0" in source
    assert 'execution["composition_operations"] == 0' in source
