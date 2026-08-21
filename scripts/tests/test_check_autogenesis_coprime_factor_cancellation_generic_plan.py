import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts/check-autogenesis-coprime-factor-cancellation-generic-plan.py"
PLAN = ROOT / "artifacts/autogenesis/coprime-factor-cancellation-generic-plan-v1.json"


class GenericCancellationPlanCheckerTests(unittest.TestCase):
    def test_committed_plan_passes(self):
        subprocess.run(["python3", str(CHECKER)], cwd=ROOT, check=True, capture_output=True, text=True)

    def test_authority_is_zero(self):
        value = json.loads(PLAN.read_text())
        value["authority"]["generic_cancellation_credit"] = 1
        with tempfile.TemporaryDirectory() as temporary:
            mutated = Path(temporary) / "plan.json"
            mutated.write_text(json.dumps(value))
            environment = os.environ.copy()
            environment["AXEYUM_GENERIC_CANCELLATION_PLAN"] = str(mutated)
            result = subprocess.run(["python3", str(CHECKER)], cwd=ROOT, env=environment, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)


if __name__ == "__main__":
    unittest.main()
