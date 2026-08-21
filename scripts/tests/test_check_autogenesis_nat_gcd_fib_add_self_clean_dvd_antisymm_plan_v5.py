from __future__ import annotations
import pathlib, subprocess
ROOT = pathlib.Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-clean-dvd-antisymm-plan-v5.py"

def test_v5_plan_passes() -> None:
    assert subprocess.run(["python3", str(CHECKER)], cwd=ROOT, check=False).returncode == 0

def test_v5_checker_binds_branch_specialization_and_zero_authority() -> None:
    source = CHECKER.read_text()
    assert "bind both hypotheses separately" in source and "all(value == 0" in source
