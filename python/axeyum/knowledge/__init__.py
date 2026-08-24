"""Read-only, typed accessors over this repository's knowledge artifacts (tier R).

``axeyum.knowledge`` is read-only *by construction*. Nothing in it writes a
ledger, admits a fact, relaxes a checker, or changes an axiom footprint; writes
go through the existing ``scripts/``, from JSON some other layer produced.

Every accessor mirrors the canonical validator for its artifact rather than
re-deriving the rules, and is tested against that validator -- same inputs, same
verdicts:

===================  ===============================================
submodule            canonical authority
===================  ===============================================
:mod:`facts`         ``scripts/validate-facts.py``
:mod:`frontier`      ``scripts/fact-frontier.py --json``/``--verify``
:mod:`operations`    ``scripts/validate-autogenesis-operations.py``
:mod:`overlay`       ``scripts/validate-autogenesis-knowledge.py``
:mod:`nursery`       ``scripts/check-autogenesis-holdout-isolation.py``
:mod:`claims`        ``scripts/validate-claims.py``
:mod:`concepts`      ``scripts/validate-foundational-concepts.py``
:mod:`math_education` the overlay pin + ``git rev-parse HEAD``
:mod:`autogenesis`   shape classification (``kind`` has 707 values)
:mod:`generated`     the dashboards' own headers
===================  ===============================================

Three rules hold everywhere in this package:

1. **Nothing found is not the same as not looked at.** An empty collection means
   the directory was read and held nothing; a missing directory raises
   :class:`FileNotFoundError` naming the path; an accessor asked about a subject
   it cannot find raises :class:`KeyError`.
2. **A refusal is a value.** ``refused-no-admissible-candidate`` from the
   frontier, ``unavailable`` / ``off-pin`` from the sibling graph, and a decline
   from a producer are answers, not exceptions.
3. **Partition questions are answered by partition, never by a count.** The
   nursery's dependency-ready set and its train+development set are both 138 and
   are different sets.
"""

from __future__ import annotations

from . import (
    autogenesis,
    claims,
    concepts,
    facts,
    frontier,
    generated,
    math_education,
    nursery,
    operations,
    overlay,
)
from ._paths import ScriptError, ScriptRun, repo_root

__all__ = [
    "ScriptError",
    "ScriptRun",
    "autogenesis",
    "claims",
    "concepts",
    "facts",
    "frontier",
    "generated",
    "math_education",
    "nursery",
    "operations",
    "overlay",
    "repo_root",
]
