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
    def test_v5_result_passes(self) -> None:
        test_v5_result_passes()

    def test_checker_requires_identical_empty_footprint_support_only_evidence(self) -> None:
        test_checker_requires_identical_empty_footprint_support_only_evidence()
