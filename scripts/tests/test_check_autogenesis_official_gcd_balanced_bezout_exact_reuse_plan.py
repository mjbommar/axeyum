import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts/check-autogenesis-official-gcd-balanced-bezout-exact-reuse-plan.py"
PLAN = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-exact-reuse-plan-v1.json"


class ExactReusePlanCheckerTests(unittest.TestCase):
    def test_committed_plan_passes(self):
        subprocess.run(["python3", str(CHECKER)], cwd=ROOT, check=True, capture_output=True, text=True)

    def test_authority_mutation_fails(self):
        original = json.loads(PLAN.read_text())
        with tempfile.TemporaryDirectory() as temporary:
            copy = Path(temporary) / "plan.json"
            original["authority"]["closed_gcd_balanced_bezout_credit"] = 1
            copy.write_text(json.dumps(original))
            environment = os.environ.copy()
            environment["AXEYUM_EXACT_REUSE_PLAN"] = str(copy)
            result = subprocess.run(["python3", str(CHECKER)], cwd=ROOT, env=environment, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)


if __name__ == "__main__":
    unittest.main()
