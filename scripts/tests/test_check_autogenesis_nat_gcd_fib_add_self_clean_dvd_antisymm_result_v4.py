from __future__ import annotations
import pathlib, subprocess
ROOT = pathlib.Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-clean-dvd-antisymm-result-v4.py"

def test_v4_decline_passes() -> None:
    assert subprocess.run(["python3", str(CHECKER)], cwd=ROOT, check=False).returncode == 0

def test_checker_binds_type_mismatch_and_zero_authority() -> None:
    source = CHECKER.read_text()
    assert "TypeMismatch" in source and "all(value == 0" in source
