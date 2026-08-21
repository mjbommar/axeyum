import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts/check-autogenesis-official-gcd-balanced-bezout-exact-reuse-result.py"
RESULT = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-exact-reuse-result-v1.json"


class ExactReuseResultCheckerTests(unittest.TestCase):
    def run_mutation(self, mutate):
        value = json.loads(RESULT.read_text())
        mutate(value)
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "result.json"
            path.write_text(json.dumps(value))
            environment = os.environ.copy()
            environment["AXEYUM_EXACT_REUSE_RESULT"] = str(path)
            return subprocess.run(["python3", str(CHECKER)], cwd=ROOT, env=environment, capture_output=True, text=True)

    def test_committed_result_passes(self):
        subprocess.run(["python3", str(CHECKER)], cwd=ROOT, check=True, capture_output=True, text=True)

    def test_axiom_mutation_fails(self):
        self.assertNotEqual(self.run_mutation(lambda value: value["theorem"]["axiom_footprint"].append("propext")).returncode, 0)

    def test_identity_mutation_fails(self):
        self.assertNotEqual(self.run_mutation(lambda value: value["reused_declaration"].__setitem__("target_declaration_sha256", "0" * 64)).returncode, 0)

    def test_authority_mutation_fails(self):
        self.assertNotEqual(self.run_mutation(lambda value: value["authority"].__setitem__("cancellation_credit", 1)).returncode, 0)


if __name__ == "__main__":
    unittest.main()
