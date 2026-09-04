#!/usr/bin/env python3
"""Controls for `scripts/check-draw7-frozen-families.py`'s licensing path.

One test per guard. Each was verified to die alone under the mutation that
removes its guard (2026-09-03, on a scratch copy of the script -- never in
the shared worktree). Set `DRAW7_SCRIPT` to point the suite at a copy.
"""
from __future__ import annotations

import importlib.util
import os
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = pathlib.Path(os.environ.get(
    "DRAW7_SCRIPT", ROOT / "scripts" / "check-draw7-frozen-families.py"))
spec = importlib.util.spec_from_file_location("draw7", SCRIPT)
draw7 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(draw7)

BEFORE = {"a-family": "held-out", "b-family": "train"}


def policy(rows) -> str:
    import json
    return json.dumps({"amendments": rows})


class Licensing(unittest.TestCase):
    def test_unamended_move_is_reported(self):
        after = {"a-family": "development", "b-family": "train"}
        self.assertEqual(draw7.compare(BEFORE, after, set()),
                         ["a-family: held-out -> development"])

    def test_matching_irreversible_amendment_licenses_the_move(self):
        after = {"a-family": "development", "b-family": "train"}
        lic = draw7.licensed_moves(policy([{"family": "a-family", "from": "held-out",
                                            "to": "development", "irreversible": True}]))
        self.assertEqual(draw7.compare(BEFORE, after, lic), [])

    def test_wrong_direction_amendment_does_not_license(self):
        after = {"a-family": "development", "b-family": "train"}
        lic = draw7.licensed_moves(policy([{"family": "a-family", "from": "held-out",
                                            "to": "train", "irreversible": True}]))
        self.assertEqual(draw7.compare(BEFORE, after, lic),
                         ["a-family: held-out -> development"])

    def test_reversible_amendment_does_not_license(self):
        lic = draw7.licensed_moves(policy([{"family": "a-family", "from": "held-out",
                                            "to": "development", "irreversible": False}]))
        self.assertEqual(lic, set())

    def test_vanished_family_is_reported_even_when_amended(self):
        after = {"b-family": "train"}
        lic = {("a-family", "held-out", "development")}
        self.assertEqual(draw7.compare(BEFORE, after, lic),
                         ["a-family: held-out -> ABSENT"])

    def test_no_licensing_argument_means_nothing_is_licensed(self):
        after = {"a-family": "development", "b-family": "train"}
        self.assertEqual(draw7.compare(BEFORE, after),
                         ["a-family: held-out -> development"])


if __name__ == "__main__":
    unittest.main()
