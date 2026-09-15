#!/usr/bin/env python3
"""Per-file SHAPE of a QF_LRA benchmark, read from the `.smt2` text.

This is a **descriptive** instrument, deliberately separate from the solver's
own trail: the trail says what our engine did, and the shape says what the file
IS.  Keeping them in two authorities is the point -- if a shape number and a
trail counter disagree, that disagreement is a finding, and it is unreachable
when one is derived from the other.

What it is NOT: a parser.  It is a token scan, and it says so in its own output
(`method=token-scan`), because the repository's standing rule is that a number
whose method is not printed beside it cannot be read against another one.  Two
consequences are stated rather than implied:

  * `let`-bound terms are NOT substituted, so `vars` counts *declared* symbols
    (from `declare-fun`/`declare-const`), which is exact, while `atoms` counts
    relational operator occurrences, which over-counts a shared atom appearing
    under two `let` uses and under-counts nothing.
  * `equalities` counts `(= ...)` occurrences at any sort, including Boolean
    `iff`, and the Boolean share is reported separately (`eq_bool_hint`) rather
    than silently folded in, because `iff` is precisely the connective
    `lra_route.rs` documents as having routed whole files to the weak engine.

Usage:  shape_census.py <corpus-root> <relative-path-list> > shapes.tsv
"""

from __future__ import annotations

import re
import sys
from fractions import Fraction
from pathlib import Path

# A relational operator token.  `\b` would not do: SMT-LIB symbols may contain
# `<`, so the anchor is the opening paren plus whitespace after the operator.
REL_RE = re.compile(r"\((<=|>=|<|>|=|distinct)[\s(]")
NUM_RE = re.compile(r"(?<![\w.])(\d+)(?:\.(\d+))?(?![\w.])")
DIV_RE = re.compile(r"\(/\s+(-?\d+)(?:\.\d+)?\s+(\d+)(?:\.\d+)?\s*\)")
DECL_RE = re.compile(r"\(declare-(?:fun|const)\s+(\|[^|]*\||[^\s()]+)")
STATUS_RE = re.compile(r"set-info\s*:status\s+(sat|unsat|unknown)")
LOGIC_RE = re.compile(r"set-logic\s+([A-Za-z_0-9]+)")
ASSERT_RE = re.compile(r"\(assert[\s(]")
# `(* c x)` / `(* x c)`: a multiplication with a numeral operand is linear.
MUL_RE = re.compile(r"\(\*[\s(]")


def digits(n: int) -> int:
    """Decimal digit count of |n|, 1 for zero."""
    n = abs(n)
    return len(str(n)) if n else 1


def shape(text: str) -> dict[str, object]:
    decls = DECL_RE.findall(text)
    rels = REL_RE.findall(text)
    # Coefficient magnitude: the largest integer literal and the largest
    # denominator appearing in a `(/ p q)` rational literal.  Reported as DIGIT
    # COUNTS, not values: the interesting quantity is the bit growth the exact
    # arithmetic has to carry, and a raw value that does not fit `i128` cannot
    # be put in a TSV column and compared.
    max_num_digits = 0
    for m in NUM_RE.finditer(text):
        whole, frac = m.group(1), m.group(2)
        d = digits(int(whole))
        if frac is not None:
            # A decimal `a.b` is the rational `ab / 10^len(b)`; its denominator
            # is what the exact engine actually carries.
            d = max(d, len(frac) + 1)
        max_num_digits = max(max_num_digits, d)
    max_den_digits = 0
    rationals = 0
    for m in DIV_RE.finditer(text):
        rationals += 1
        try:
            q = Fraction(int(m.group(1)), int(m.group(2)))
        except ZeroDivisionError:
            continue
        max_den_digits = max(max_den_digits, digits(q.denominator))
    for m in re.finditer(r"(?<![\w.])(\d+)\.(\d+)(?![\w.])", text):
        max_den_digits = max(max_den_digits, len(m.group(2)) + 1)

    eq = sum(1 for r in rels if r == "=")
    # Boolean `=` (an `iff`) cannot be told from an arithmetic `=` without sorts.
    # The hint is `(= ` immediately followed by a token that is a known Boolean
    # connective or a `let`-bound Boolean name -- reported as a HINT and nothing
    # more, so a reader never mistakes it for a typed count.
    eq_bool_hint = len(re.findall(r"\(=\s+\((?:and|or|not|=>|<=|>=|<|>)\b", text))

    status_m = STATUS_RE.search(text)
    logic_m = LOGIC_RE.search(text)
    return {
        "vars": len(decls),
        "asserts": len(ASSERT_RE.findall(text)),
        "atoms": len(rels),
        "equalities": eq,
        "eq_bool_hint": eq_bool_hint,
        "strict": sum(1 for r in rels if r in ("<", ">")),
        "muls": len(MUL_RE.findall(text)),
        "rational_lits": rationals,
        "max_numeral_digits": max_num_digits,
        "max_denominator_digits": max_den_digits,
        "status": status_m.group(1) if status_m else "none",
        "logic": logic_m.group(1) if logic_m else "none",
        "bytes": len(text),
    }


COLUMNS = [
    "file",
    "method",
    "bytes",
    "logic",
    "status",
    "vars",
    "asserts",
    "atoms",
    "equalities",
    "eq_bool_hint",
    "eq_share",
    "strict",
    "muls",
    "rational_lits",
    "max_numeral_digits",
    "max_denominator_digits",
]


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        sys.stderr.write(__doc__ or "")
        return 2
    root, listing = Path(argv[1]), Path(argv[2])
    rows = [line.strip() for line in listing.read_text().splitlines() if line.strip()]
    missing = [r for r in rows if not (root / r).is_file()]
    if missing:
        for m in missing:
            sys.stderr.write(f"MISSING\t{m}\n")
        sys.stderr.write(f"shape_census: {len(missing)} of {len(rows)} unreadable\n")
        return 2
    print("\t".join(COLUMNS))
    for rel in rows:
        s = shape((root / rel).read_text(errors="replace"))
        s["file"] = rel
        s["method"] = "token-scan"
        atoms = int(s["atoms"]) or 1
        s["eq_share"] = f"{int(s['equalities']) / atoms:.3f}"
        print("\t".join(str(s[c]) for c in COLUMNS))
    sys.stderr.write(f"shape_census: {len(rows)} rows, 0 unreadable\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
