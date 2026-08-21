from __future__ import annotations
import pathlib, subprocess
ROOT = pathlib.Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-clean-dvd-antisymm-result-v5.py"

def test_v5_result_passes() -> None:
    assert subprocess.run(["python3", str(CHECKER)], cwd=ROOT, check=False).returncode == 0

def test_checker_requires_identical_empty_footprint_support_only_evidence() -> None:
    source = CHECKER.read_text()
    assert 'run["source_theorems"] == run["target_theorems"]' in source
    assert 'not theorem["axiom_footprint"]' in source
    assert '"target_credit": 0' in source
