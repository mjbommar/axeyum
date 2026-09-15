#!/usr/bin/env python3
"""REAL-OPAQUE E3 -- count `Sat` CONSTRUCTION sites outside `#[cfg(test)]`.

Why this is a Python scanner and not a `grep`: the first version of this
enumeration cut each file at its FIRST `^#[cfg(test)]` line, on the assumption
that it marks the test module at the end. In both files it marks a test-only
*helper item* in the middle -- `lra.rs:2482` (`cold_int_system`) and
`dpll_lia.rs:1730` -- so the cut silently discarded 2,397 and 3,133 lines of
PRODUCTION code, including a whole `CheckResult::Sat` construction in
`check_with_lra_simplex`. The output looked clean and was a measurement of the
accepted subset. That is the failure this file exists to not repeat, so it
prints the raw count, the skipped count and the kept count, and they must add up.

A `#[cfg(test)]` region is skipped by brace balance from the attribute's item to
the line whose closing brace returns the depth to zero; the scanner ASSERTS that
line is `}` at column 0, so a shape it cannot handle is a hard failure, never a
silent omission.
"""

import re
import sys

PATTERNS = {
    "Decision::Sat": re.compile(r"Decision::Sat\("),
    "CheckResult::Sat": re.compile(r"CheckResult::Sat\("),
    "LraOpaqueOutcome": re.compile(r"LraOpaqueOutcome::"),
}
# A `Sat(_)` / `Sat(model)` inside a `match` ARM is a read, not a construction,
# when the scrutinee is being destructured. We report both and separate the
# pattern-only spellings, which are unambiguous.
PATTERN_ONLY = re.compile(r"(Decision|CheckResult)::Sat\(_\)")


def test_regions(lines):
    """Half-open [start, end) line index ranges covered by `#[cfg(test)]`."""
    regions = []
    i = 0
    n = len(lines)
    while i < n:
        if lines[i].startswith("#[cfg(test)]"):
            # Walk forward to the item's opening brace, then to its close.
            j = i
            depth = 0
            opened = False
            while j < n:
                depth += lines[j].count("{") - lines[j].count("}")
                if "{" in lines[j]:
                    opened = True
                if opened and depth <= 0:
                    break
                j += 1
            if not opened:
                raise SystemExit(f"cfg(test) item at line {i + 1} has no brace body")
            assert lines[j].rstrip() == "}", (
                f"cfg(test) region starting line {i + 1} does not end at a "
                f"column-0 close brace; line {j + 1} is {lines[j]!r}"
            )
            regions.append((i, j + 1))
            i = j + 1
        else:
            i += 1
    return regions


def main(paths):
    for path in paths:
        lines = open(path).read().splitlines()
        regions = test_regions(lines)
        skipped = sum(b - a for a, b in regions)
        in_test = [False] * len(lines)
        for a, b in regions:
            for k in range(a, b):
                in_test[k] = True
        print(f"== {path} ==")
        print(f"   lines={len(lines)} cfg(test)_regions={len(regions)} lines_in_test={skipped}")
        for name, pat in PATTERNS.items():
            raw = [k for k, line in enumerate(lines) if pat.search(line)]
            prod = [k for k in raw if not in_test[k]]
            test = [k for k in raw if in_test[k]]
            assert len(prod) + len(test) == len(raw)
            ctor = [k for k in prod if not PATTERN_ONLY.search(lines[k])]
            print(
                f"   {name}: raw={len(raw)} in_test={len(test)} production={len(prod)} "
                f"production_non_pattern={len(ctor)}"
            )
            for k in ctor:
                print(f"      {path}:{k + 1}: {lines[k].strip()}")
        print()


if __name__ == "__main__":
    main(sys.argv[1:])
