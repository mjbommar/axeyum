from __future__ import annotations

import pathlib
import subprocess


ROOT = pathlib.Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-clean-dvd-antisymm-result-v2.py"


def test_retained_v2_decline_passes() -> None:
    result = subprocess.run(["python3", str(CHECKER)], cwd=ROOT, check=False)
    assert result.returncode == 0


def test_checker_is_bound_to_manifest_digest() -> None:
    source = CHECKER.read_text()
    assert "EXPECTED_MANIFEST_SHA256" in source
    assert "sha256(MANIFEST) == EXPECTED_MANIFEST_SHA256" in source


def test_checker_requires_zero_authority() -> None:
    source = CHECKER.read_text()
    assert '\"target_credit\": 0' in source
    assert '\"ledger_writes\": 0' in source
    assert 'execution[\"composition_operations\"] == 0' in source


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
    def test_retained_v2_decline_passes(self) -> None:
        test_retained_v2_decline_passes()

    def test_checker_is_bound_to_manifest_digest(self) -> None:
        test_checker_is_bound_to_manifest_digest()

    def test_checker_requires_zero_authority(self) -> None:
        test_checker_requires_zero_authority()
