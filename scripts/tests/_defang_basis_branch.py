#!/usr/bin/env python3
"""Copy `check-admission-limit-basis.py` with one `check_basis` branch removed.

Used only by `test-admission-limit-basis-control.sh` step 6, which deletes each
guard in turn and requires that EXACTLY ONE of its four registry mutants stops
being caught. A guard removable with every step still red is decoration.

    _defang_basis_branch.py <checker> <out> <branch-anchor>

Exits non-zero when the anchor is absent or ambiguous: a mutation applied to
nothing, reported as a clean run, is the failure mode this whole control exists
to rule out. Never writes into the repository — `out` is the caller's scratch
directory.
"""

import sys
from pathlib import Path


def main(argv: list[str]) -> int:
    if len(argv) != 4:
        print(__doc__, file=sys.stderr)
        return 2
    src = Path(argv[1]).read_text(encoding="utf-8")
    anchor = argv[3]
    n = src.count(anchor)
    if n != 1:
        print(
            f"anchor occurs {n} time(s), expected exactly 1: {anchor!r}",
            file=sys.stderr,
        )
        return 2
    Path(argv[2]).write_text(
        src.replace(anchor, anchor + "\n        return None", 1), encoding="utf-8"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
