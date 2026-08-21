from __future__ import annotations

import pathlib
import subprocess


ROOT = pathlib.Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-exact-plan.py"


def test_exact_plan_passes() -> None:
    assert subprocess.run(["python3", str(CHECKER)], cwd=ROOT, check=False).returncode == 0


def test_checker_requires_clean_replacements_and_zero_authority() -> None:
    source = CHECKER.read_text()
    assert '"Nat.gcd_comm" in shortcuts' in source
    assert '"Nat.dvd_antisymm" in shortcuts' in source
    assert 'acceptance["target_axiom_footprint"] == []' in source
    assert "all(value == 0" in source
