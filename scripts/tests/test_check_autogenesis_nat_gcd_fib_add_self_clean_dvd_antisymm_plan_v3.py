from __future__ import annotations

import pathlib
import subprocess


ROOT = pathlib.Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-clean-dvd-antisymm-plan-v3.py"


def test_v3_plan_passes() -> None:
    result = subprocess.run(["python3", str(CHECKER)], cwd=ROOT, check=False)
    assert result.returncode == 0


def test_v3_plan_checker_binds_predecessor_and_exact_leaf() -> None:
    source = CHECKER.read_text()
    assert "sha256(PREDECESSOR)" in source
    assert '== [\"Nat.zero_mul\"]' in source
    assert 'len(construction[\"transport_roots\"]) == 3' in source


def test_v3_plan_checker_requires_zero_authority() -> None:
    assert "all(value == 0 for value in plan[\"authority\"].values())" in CHECKER.read_text()


# --- `python3 -m unittest` collection ---------------------------------------
# `unittest` collects `TestCase` METHODS, never module-level functions, so this
# file reported `Ran 0 tests` and exited 5 under the invocation EVERY gate in
# this repository uses -- while passing when run by hand under pytest. A suite
# that collects nothing is the repository's oldest trap wearing a green shirt.
#
# The wrapper below changes nothing any function asserts; it only makes them
# reachable. `scripts/run-python-controls.py` fails any suite that runs zero
# tests, so this cannot silently regress.
import unittest  # noqa: E402


class BareFunctionControls(unittest.TestCase):
    def test_v3_plan_passes(self) -> None:
        test_v3_plan_passes()

    def test_v3_plan_checker_binds_predecessor_and_exact_leaf(self) -> None:
        test_v3_plan_checker_binds_predecessor_and_exact_leaf()

    def test_v3_plan_checker_requires_zero_authority(self) -> None:
        test_v3_plan_checker_requires_zero_authority()
