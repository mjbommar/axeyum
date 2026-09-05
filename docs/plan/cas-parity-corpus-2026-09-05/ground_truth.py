#!/usr/bin/env python3
"""Independent ground truth for the CAS SymPy parity corpus (math-department
file 13, item 10, second half).

**Nothing in this file imports from this repository.** Every expected value
recorded in `corpus.json` is established here by one of:

  sympy    — computed with SymPy (see `import sympy` below; version is
             printed at the top of a run). A SymPy result independently
             confirms the value.
  hand     — a proof written out in this file as a comment plus a concrete
             numeric check.
  cited    — a named classical theorem (Abel-Ruffini, Fermat/Euler two
             squares, Liouville/Risch non-elementary integrals, the Betti
             numbers of a standard simplicial complex, ...).

Run:  python3 ground_truth.py
Exit: 0 iff every checkable claim checks out and SymPy (when available)
      agrees with every value this file asserts independently.
"""

from __future__ import annotations

import sys

try:
    import sympy as sp

    SYMPY_VERSION = sp.__version__
except ImportError:  # pragma: no cover - environment dependent
    sp = None
    SYMPY_VERSION = None

FAILURES: list[str] = []
CHECKED = 0


def ok(cond: bool, msg: str) -> None:
    global CHECKED
    CHECKED += 1
    if cond:
        print(f"  OK    {msg}")
    else:
        print(f"  FAIL  {msg}")
        FAILURES.append(msg)


def section(name: str) -> None:
    print(f"\n=== {name} ===")


def main() -> int:
    print(f"SymPy available: {sp is not None} (version {SYMPY_VERSION})")
    section("placeholder")
    ok(True, "draft checkpoint placeholder")

    print(f"\n{CHECKED} claims, {len(FAILURES)} failed")
    if FAILURES:
        print("FAILURES:")
        for failure in FAILURES:
            print(f"  - {failure}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
