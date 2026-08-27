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
    def test_exact_plan_passes(self) -> None:
        test_exact_plan_passes()

    def test_checker_requires_clean_replacements_and_zero_authority(self) -> None:
        test_checker_requires_clean_replacements_and_zero_authority()
