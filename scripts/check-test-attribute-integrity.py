#!/usr/bin/env python3
"""Fail when a `#[test]` attribute is duplicated or separated from its function.

WHY THIS EXISTS. On 2026-08-29 a merge performed with
`lane-merge-additive.py splice --anchor 'fn some_test('` inserted the spliced
items BETWEEN a `#[test]` attribute and the function it decorates. The result:
one attribute bound to the wrong function, another duplicated, and **one test
silently never ran**.

`cargo test` reported a healthy nonzero count throughout. "Confirm a NONZERO
test count" is the check this repository leans on hardest and it CANNOT see
this -- the suite still has plenty of tests, just not the one you think.
It surfaced only as an incidental `clippy -D warnings` duplicate-attribute
diagnostic, and FOUR separate lanes had to repair it before it was gated.

THE RULE. After a `#[test]` line, skipping further attributes and comments,
the next code line must begin a function. Two `#[test]`s in one attribute run
is a duplicate. Both are checked here.

Exit 1 on any finding, naming file:line. Exit 0 with a counted summary
otherwise -- the count is printed so a run that scanned nothing cannot read
as a pass.
"""

import re
import sys
from pathlib import Path

TEST_ATTR = re.compile(r"^\s*#\[(?:\w+::)*test\]\s*$")
ATTR = re.compile(r"^\s*#\[")
COMMENT = re.compile(r"^\s*(//|/\*|\*)")
FN = re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:async\s+)?(?:unsafe\s+)?(?:extern\s+\"[^\"]*\"\s+)?fn\s")


def scan(path):
    """Return a list of (line_number, kind, detail) findings for one file."""
    findings = []
    lines = path.read_text(encoding="utf-8", errors="replace").split("\n")
    i = 0
    while i < len(lines):
        if not TEST_ATTR.match(lines[i]):
            i += 1
            continue
        start = i
        seen_test = 1
        j = i + 1
        # Walk the rest of the attribute run: further attributes, comments and
        # blanks. An attribute may SPAN LINES (`#[allow(\n  clippy::foo,\n)]`),
        # so consume by bracket balance -- matching only the opening line
        # stops inside the attribute and reports a false positive, which is
        # how the first draft of this gate flagged three healthy files.
        while j < len(lines):
            line = lines[j]
            if ATTR.match(line):
                if TEST_ATTR.match(line):
                    seen_test += 1
                depth = line.count("[") - line.count("]")
                j += 1
                while j < len(lines) and depth > 0:
                    depth += lines[j].count("[") - lines[j].count("]")
                    j += 1
                continue
            if COMMENT.match(line) or not line.strip():
                j += 1
                continue
            break
        if seen_test > 1:
            findings.append((start + 1, "duplicate-test-attribute",
                             f"{seen_test} `#[test]` attributes in one run"))
        if j >= len(lines) or not FN.match(lines[j]):
            got = lines[j].strip()[:60] if j < len(lines) else "<end of file>"
            findings.append((start + 1, "test-attribute-without-function",
                             f"next code line is not a function: {got!r}"))
        i = max(j, start + 1)
    return findings


def main(argv):
    roots = [Path(a) for a in argv[1:]] or [Path("crates")]
    files = sorted(p for root in roots for p in root.rglob("*.rs"))
    if not files:
        print("check-test-attribute-integrity: NO .rs FILES SCANNED -- wrong root?", file=sys.stderr)
        return 2
    bad = 0
    attrs = 0
    for p in files:
        text = p.read_text(encoding="utf-8", errors="replace")
        attrs += sum(1 for line in text.split("\n") if TEST_ATTR.match(line))
        for line_no, kind, detail in scan(p):
            print(f"{p}:{line_no}: {kind}: {detail}")
            bad += 1
    print(f"check-test-attribute-integrity: {len(files)} files, {attrs} `#[test]` attributes, {bad} finding(s)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
