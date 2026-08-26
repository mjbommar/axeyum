import copy
import importlib.util
import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-retrieved-induction-type-slice-replay.py"
SPEC = importlib.util.spec_from_file_location("type_slice_replay_check", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class RetrievedInductionTypeSliceReplayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.mapping = json.loads(MODULE.MAPPING.read_text())
        cls.replay = json.loads(MODULE.REPLAY.read_text())

    def test_live_replay_is_accepted(self):
        result = MODULE.validate(self.mapping, self.replay)
        self.assertEqual(result["accepted"], 25)
        self.assertEqual(result["distinct_abstractions"], 14)
        self.assertEqual(result["normalized_receipts"], 3)

    def test_accepted_row_cannot_become_a_decline(self):
        replay = copy.deepcopy(self.replay)
        replay["rows"][0]["outcome"] = "decline:selection"
        replay["observation_sha256"] = MODULE.canonical_digest(
            {key: value for key, value in replay.items() if key != "observation_sha256"}
        )
        with self.assertRaisesRegex(ValueError, "not accepted"):
            MODULE.validate(self.mapping, replay)

    def test_receipt_cannot_retain_a_theorem(self):
        replay = copy.deepcopy(self.replay)
        replay["rows"][0]["receipt"]["retained"][0]["kind"] = "theorem"
        receipt = replay["rows"][0]["receipt"]
        receipt["receipt_sha256"] = MODULE.canonical_digest(
            {key: value for key, value in receipt.items() if key != "receipt_sha256"}
        )
        replay["observation_sha256"] = MODULE.canonical_digest(
            {key: value for key, value in replay.items() if key != "observation_sha256"}
        )
        with self.assertRaisesRegex(ValueError, "retained a trusted declaration"):
            MODULE.validate(self.mapping, replay)

    def test_outcome_selection_cannot_be_hidden(self):
        replay = copy.deepcopy(self.replay)
        del replay["population_selection"]
        replay["observation_sha256"] = MODULE.canonical_digest(
            {key: value for key, value in replay.items() if key != "observation_sha256"}
        )
        with self.assertRaisesRegex(ValueError, "contract or source binding"):
            MODULE.validate(self.mapping, replay)


if __name__ == "__main__":
    unittest.main()
