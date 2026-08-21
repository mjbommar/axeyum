"""A control module that FAILS, so the harness's baseline guard has something to refuse.

`mutation_controls.py` may not report a death against a suite that was already
red -- every kill would be free.  Nothing checked that the refusal works, so this
is what it is pointed at.
"""

from __future__ import annotations

import unittest


class AlreadyRed(unittest.TestCase):
    def test_this_suite_is_red_on_purpose(self) -> None:
        self.fail("red on purpose: the harness must refuse to mutate against this")
