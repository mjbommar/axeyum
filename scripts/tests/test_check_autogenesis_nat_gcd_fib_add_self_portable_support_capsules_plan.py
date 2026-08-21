from __future__ import annotations
import pathlib, subprocess
ROOT = pathlib.Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-portable-support-capsules-plan.py"

def test_capsule_plan_passes() -> None:
    assert subprocess.run(["python3", str(CHECKER)], cwd=ROOT, check=False).returncode == 0

def test_checker_requires_external_proof_storage_and_zero_target_authority() -> None:
    source = CHECKER.read_text()
    assert "proof-bearing NDJSON remains in the sealed external pack" in source
    assert 'plan["budget"]["max_exact_target_submissions"]' in source
    assert "all(value == 0" in source
