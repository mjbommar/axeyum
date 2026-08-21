"""A miniature checker, so `mutation_controls.py self-demo` has something real to break.

This is not a toy standing in for a gate; it is the *fixture* half of a control
over the mutation harness itself.  Its shape is chosen so that four one-line
mutations produce one of each outcome the harness must be able to tell apart:

* ``if n < 0`` is driven by a control  -> deleting it must be ``killed 1``
* ``if n > 100`` is driven by nothing  -> deleting it must be ``SURVIVED``
* removing the ``def`` line's colon    -> must be ``DID NOT BUILD``

The fourth (``DID NOT RUN``) is a mutation of the control module beside this
one, because "the suite executed zero tests" is a property of the suite.

Keep the two guards independently observable.  If one control could fail for
either reason, the demo would prove nothing -- CLAUDE.md records six of seven
guards in one suite being removable because they all rejected through one
shared check.
"""

from __future__ import annotations


def classify(n: int) -> str:
    if n < 0:
        raise ValueError("negative")
    if n > 100:
        return "big"
    return "small"
