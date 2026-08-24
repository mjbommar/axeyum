"""Session-level guards for the Python gate.

The one rule this file exists for: **a run that collected zero tests must fail.**
An inert gate that exits 0 while checking nothing is the failure mode this
repository has hit repeatedly (a corpus sweep that printed "running 0 tests ...
ok" for 15 days; a capability ratchet documented without its feature flag). A
pytest invocation with a wrong path, a broken import, or a stale marker
expression prints ``no tests ran`` and exits 5 -- but ``-q`` plus a wrapper that
only looks at "did it print a traceback" reads that as fine.
"""

from __future__ import annotations

import pytest

_COLLECTED = "_axeyum_collected"


def pytest_collection_modifyitems(session: pytest.Session, config, items) -> None:
    """Record how many tests were collected, for :func:`pytest_sessionfinish`."""
    setattr(session, _COLLECTED, len(items))


def pytest_sessionfinish(session: pytest.Session, exitstatus: int) -> None:
    """Fail the session when nothing was collected."""
    collected = getattr(session, _COLLECTED, 0)
    print(f"\nPYTEST|collected={collected}")
    if collected == 0:
        print("PYTEST|FAIL empty collection -- an inert gate is worse than no gate")
        session.exitstatus = 1
