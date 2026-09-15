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

**Braces inside string literals and comments are not braces.** The first version
counted them, and on the merged ADR-2060 tree it walked off the end of the file
because that ADR's own `declared_variants` helper contains
`format!("\nenum {enum_name} {{\n")` — two opening braces in a string with no
match. It failed loudly rather than guessing, which is what it is for; the fix
is `code_only`, which strips line comments, block comments, string literals and
char literals before any brace is counted. Raw strings would need more and none
exist in these files, so their presence is a hard failure too.
"""

import re
import sys

PATTERNS = {
    "Decision::Sat": re.compile(r"Decision::Sat\("),
    "CheckResult::Sat": re.compile(r"CheckResult::Sat\("),
    "LraOpaqueOutcome": re.compile(r"LraOpaqueOutcome::"),
    # E1 belongs here too, and not in the shell script's bare `grep`: after the
    # ADR-2060 merge that grep reported THREE `lra::Collector` construction
    # sites, and the third is a test fixture. The production count is the one
    # the sat-exit closure rests on, so it is counted the same way as the rest.
    "Collector::default()": re.compile(r"\bCollector::default\(\)"),
    "Collector { (literal)": re.compile(r"\bCollector \{"),
}
# A `Sat(_)` / `Sat(model)` inside a `match` ARM is a read, not a construction,
# when the scrutinee is being destructured. We report both and separate the
# pattern-only spellings, which are unambiguous.
PATTERN_ONLY = re.compile(r"(Decision|CheckResult)::Sat\(_\)")
# `r"` / `r#"` where the `r` begins a token, not where it ends an identifier.
RAW_STRING = re.compile(r'(?<![A-Za-z0-9_])r#*"')


def code_only(line, in_block_comment):
    """The code part of one line: string/char literal bodies and comments gone.

    Returns `(stripped, still_in_block_comment)`. Only braces in the stripped
    text are real braces.
    """
    # A raw-string prefix is an `r` that is NOT part of an identifier — the
    # plain substring test flags `real_var("x")` and every other identifier
    # ending in `r` followed by a quote, which is most of this file.
    if RAW_STRING.search(line):
        raise SystemExit(
            f"raw string literal in {line!r}: this stripper does not handle them and "
            f"will not guess. Extend it rather than letting it miscount."
        )
    out = []
    i = 0
    n = len(line)
    while i < n:
        if in_block_comment:
            if line.startswith("*/", i):
                in_block_comment = False
                i += 2
            else:
                i += 1
            continue
        if line.startswith("//", i):
            break
        if line.startswith("/*", i):
            in_block_comment = True
            i += 2
            continue
        if line[i] == '"':
            i += 1
            while i < n:
                if line[i] == "\\":
                    i += 2
                    continue
                if line[i] == '"':
                    i += 1
                    break
                i += 1
            continue
        if line[i] == "'":
            # A lifetime (`'a`) is not a char literal; a char literal is at most
            # `'\u{7f}'`. Treat it as a literal only when a closing quote is near.
            close = line.find("'", i + 1)
            if close != -1 and close - i <= 8:
                i = close + 1
                continue
            i += 1
            continue
        out.append(line[i])
        i += 1
    return "".join(out), in_block_comment


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
            in_block = False
            while j < n:
                code, in_block = code_only(lines[j], in_block)
                depth += code.count("{") - code.count("}")
                if "{" in code:
                    opened = True
                if opened and depth <= 0:
                    break
                j += 1
            if not opened:
                raise SystemExit(f"cfg(test) item at line {i + 1} has no brace body")
            if j >= n:
                raise SystemExit(
                    f"cfg(test) region starting at line {i + 1} never returns to brace "
                    f"depth 0 before EOF (depth {depth} at EOF). This counter cannot be "
                    f"trusted on that shape and refuses rather than guessing -- which is "
                    f"the whole point of it. Fix the counter, do not relax the assert."
                )
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
