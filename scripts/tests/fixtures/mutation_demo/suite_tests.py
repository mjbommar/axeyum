"""Controls for the `self-demo` fixture subject.

Deliberately does NOT cover `classify(200)`: the uncovered guard is what makes
`SURVIVED` a real outcome to demonstrate rather than a contrived one.

Named `suite_tests.py`, not `test_*.py`, so `check-control-tests-reachable.py`
does not count a fixture as a control in its own right.
"""

from __future__ import annotations

import importlib.util
import pathlib
import sys
import unittest

SPEC = importlib.util.spec_from_file_location(
    "mutation_demo_subject", pathlib.Path(__file__).resolve().parent / "subject.py"
)
assert SPEC is not None and SPEC.loader is not None
SUBJECT = importlib.util.module_from_spec(SPEC)
sys.modules["mutation_demo_subject"] = SUBJECT
SPEC.loader.exec_module(SUBJECT)


class DemoControls(unittest.TestCase):
    def test_negative_is_refused(self) -> None:
        with self.assertRaises(ValueError):
            SUBJECT.classify(-1)

    def test_small_is_small(self) -> None:
        self.assertEqual(SUBJECT.classify(5), "small")


if __name__ == "__main__":
    unittest.main()
