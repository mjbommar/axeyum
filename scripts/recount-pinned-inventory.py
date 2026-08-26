#!/usr/bin/env python3
r"""Recount a pinned declaration-inventory array by COUNTING its entries.

The pin is `let expected: [(&str, crate::NameId, &str); N] = [ ... ];` in a
prelude's `*_tests.rs`. `N` must equal the number of entries, and the standing
rule is to recompute it by counting rather than by incrementing.

The trap this script exists for: **entries are not one per line.** rustfmt wraps
any entry whose name is long across five lines, beginning with a bare `(` on its
own line. So the obvious count -- lines that look like `("Name", p.f, "kind"),`
-- silently undercounts. Measured 2026-08-26 on `creal_tests.rs`: 210 such lines
against a true 283, and the wrong number was written into the file before the
discrepancy was noticed. It fails closed (the suite refuses to compile), but it
costs a push battery, which is several minutes here.

An entry therefore starts at either form, and only those two:

    ^        \("        -- a single-line entry
    ^        \($        -- the head of a wrapped entry

Exit 0 when the pin is correct, 1 when it is not (rewriting it unless --check).
"""

import argparse
import re
import sys

DECL = re.compile(r"let expected: \[\(&str, crate::NameId, &str\); (\d+)\] = \[")
SINGLE = re.compile(r'^        \("')
WRAPPED = re.compile(r"^        \($")


def recount(path, check_only):
    lines = open(path).read().split("\n")
    try:
        i = next(k for k, l in enumerate(lines) if DECL.search(l))
    except StopIteration:
        print(f"{path}: no pinned inventory array found", file=sys.stderr)
        return 2
    try:
        j = next(k for k in range(i + 1, len(lines)) if lines[k].strip() == "];")
    except StopIteration:
        print(f"{path}: pinned array is not terminated by `];`", file=sys.stderr)
        return 2

    body = lines[i + 1 : j]
    single = sum(1 for l in body if SINGLE.match(l))
    wrapped = sum(1 for l in body if WRAPPED.match(l))
    counted = single + wrapped
    declared = int(DECL.search(lines[i]).group(1))

    print(
        f"{path}: declared={declared} counted={counted} "
        f"(single={single} wrapped={wrapped})"
    )
    if declared == counted:
        return 0
    if check_only:
        print(f"{path}: PIN WRONG -- declared {declared}, counted {counted}")
        return 1
    lines[i] = DECL.sub(
        lambda m: m.group(0).replace(f"; {declared}]", f"; {counted}]"), lines[i]
    )
    open(path, "w").write("\n".join(lines))
    print(f"{path}: REWROTE {declared} -> {counted}")
    return 1


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("paths", nargs="+")
    ap.add_argument(
        "--check",
        action="store_true",
        help="report without rewriting (for gates)",
    )
    args = ap.parse_args()
    worst = 0
    for p in args.paths:
        worst = max(worst, recount(p, args.check))
    return worst


if __name__ == "__main__":
    sys.exit(main())
