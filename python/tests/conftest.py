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


# --- Hypothesis ---------------------------------------------------------------
#
# `hypothesis` is imported unconditionally and NOT guarded by an
# `importorskip`: it is a declared member of the `dev` dependency group that
# every gate installs, and a run that quietly skipped the property suites
# because a dev dependency was missing is the same inert gate this file exists
# to refuse. A missing `hypothesis` must be loud.
#
# `derandomize=True` is what makes the property suites obey this repository's
# determinism promise: the same commit generates the same examples on every
# host, so a failure is reproducible from the report alone and a green run is
# not luck. It also disables the example database, which would otherwise be a
# fixed-name file every lane in this shared checkout writes to.
#
# `deadline=None` because these properties call the solver, the CAS and the
# kernel: a per-example wall-clock deadline measures how loaded this box is,
# not whether the property holds. `progress_frontier`'s reference-frame note
# (docs/research/08-planning/frontier-ratchet-reference-frame.md) is the same
# lesson one layer down.
from hypothesis import HealthCheck, settings

settings.register_profile(
    "axeyum",
    derandomize=True,
    max_examples=200,
    deadline=None,
    # `data_too_large`/`filter_too_much` stay ON -- they are the health checks
    # that catch a generator which cannot reach the shape it claims to test.
    # Only the wall-clock one is suppressed, for the reason above.
    suppress_health_check=[HealthCheck.too_slow],
    print_blob=True,
)
settings.load_profile("axeyum")
