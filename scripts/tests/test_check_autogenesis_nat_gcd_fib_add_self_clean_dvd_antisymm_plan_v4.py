from __future__ import annotations
import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-clean-dvd-antisymm-plan-v4.py"


def test_v4_plan_passes() -> None:
    assert subprocess.run(["python3", str(CHECKER)], cwd=ROOT, check=False).returncode == 0


def test_v4_checker_binds_native_positivity_and_zero_authority() -> None:
    source = CHECKER.read_text()
    assert "Nat.le_succ_succ" in source and "Nat.zero_le" in source
    assert "all(value == 0" in source
