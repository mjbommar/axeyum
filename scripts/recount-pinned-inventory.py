#!/usr/bin/env python3
r"""Recount a pinned array length by COUNTING its entries.

A *pinned list* is a Rust array whose length is written down beside it:

    let expected: [(&str, crate::NameId, &str); 432] = [ ... ];   // inventory
    fn derived_laws(p: &IntPrelude) -> [crate::NameId; 156] { [ ... ] }
    const RING_BINDER_NAMES: [&str; 30] = [ ... ];

`N` must equal the number of entries, and the standing rule is to recompute it
by COUNTING rather than by incrementing.

Why the tool exists
-------------------
Two lanes each bumping the pin *correctly against their own base* produce a
merge that does not compile: git merges the entry lines cleanly (they are
different lines) and leaves the declared size short. CLAUDE.md records this
happening eight times in one day, and again on 2026-08-29 for `derived_laws`.

And counting by hand is the thing that goes wrong. Entries are **not one per
line** -- rustfmt wraps any entry whose name is long across five lines,
beginning with a bare `(` on its own line -- so the obvious count (lines that
look like an entry) silently undercounts. Measured 2026-08-26 on
`creal_tests.rs`: 210 such lines against a true 283, and the wrong number was
written into the file before the discrepancy was noticed.

How it counts
-------------
NOT by line shape. The body of the array literal is scanned with a
bracket-depth counter and entries are separated by **top-level commas**, after
comments, string literals and char literals have been masked out. That is what
makes one engine cover every shape in the tree rather than one of four:
measured 2026-08-29, the tree had 12 pinned-list sites across 4 shapes and the
line-shape version recognized only `[(&str, crate::NameId, &str); N]`, so
running it on `int_prelude_tests.rs` answered "no pinned inventory array
found" -- a correct answer to the question it asked, and a false negative for
the question being asked.

Masking is not optional cleanup, it is load-bearing twice over:

  * This repository's doc comments are full of deliberately unbalanced
    brackets (`[0,n)`, intra-doc links), which wreck a depth counter.
  * `creal/inventory.rs`'s module docs QUOTE a pin declaration in prose to
    explain why that pin is gone. An unmasked scan matches the prose and then
    fails on it as "not terminated by `];`". The control suite worked around
    this with an anchored grep and noted that the anchor "is also the right fix
    for the tool"; masking is that fix, and it is strictly stronger than an
    anchor (an anchored scan still matches an indented `//!` code block).

`single=` / `wrapped=` in the output are a diagnostic, not the count: they
split the counted entries by whether the entry's own text fits on one line.
A pin that is wrong with `wrapped` nonzero is the measured failure above.

Deleting a pin is often the better answer
-----------------------------------------
This tool makes a pin cheap to maintain; it does not make a pin worth having.
A length pin answers "is this list internally consistent with a number
somebody wrote above it", never "is this list complete". Where an
authority-derived assertion already answers completeness -- e.g.
`every_int_declaration_is_checked_and_axiom_free` reading
`kernel.environment()` directly -- the pin catches nothing that assertion does
not, and is pure merge friction. That is why `creal_tests.rs`'s 432-entry pin
was deleted rather than kept (see `crates/axeyum-lean-kernel/src/creal/
inventory.rs`). Survey and per-site judgments:
`docs/plan/status/248-pin-recount-shapes.md`.

Exit 0 when every pin in the file is correct, 1 when one is not (rewriting it
unless --check), 2 when the file has no pinned array at all.
"""

import argparse
import re
import sys

# A pinned array TYPE: `[Elem; N]`. `Elem` may not contain `;` or a bracket,
# which is true of every shape in the tree (`crate::NameId`, `&str`,
# `(&str, crate::NameId, &str)`).
ARRAY_TYPE = re.compile(r"\[\s*(?P<elem>[^\[\];]+?)\s*;\s*(?P<n>\d+)\s*\]")

# Between the type annotation and the `[` that opens the literal there may be
# only these: `= ` for a let/const/static, or `{` for a function whose body is
# the literal. Anything else means this `[T; N]` is not a definition site.
_BRIDGE = set(" \t\r\n={")

OPEN = {"(": ")", "[": "]", "{": "}"}
CLOSE = {")": "(", "]": "[", "}": "{"}


def mask(src):
    """Return `src` with comments, strings and char literals blanked to spaces.

    Length and newlines are preserved so every offset stays valid. Handles
    nested block comments, raw strings with any hash count, and does NOT
    mistake a lifetime (`'a`) for a char literal.
    """
    out = list(src)
    i, n = 0, len(src)

    def blank(a, b):
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "

    while i < n:
        c = src[i]
        if c == "/" and i + 1 < n and src[i + 1] == "/":
            j = src.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        elif c == "/" and i + 1 < n and src[i + 1] == "*":
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/*", j):
                    depth += 1
                    j += 2
                elif src.startswith("*/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            blank(i, j)
            i = j
        elif c == "r" and i + 1 < n and src[i + 1] in '"#':
            k = i + 1
            hashes = 0
            while k < n and src[k] == "#":
                hashes += 1
                k += 1
            if k < n and src[k] == '"':
                term = '"' + "#" * hashes
                j = src.find(term, k + 1)
                j = n if j < 0 else j + len(term)
                blank(i, j)
                i = j
            else:
                i += 1
        elif c == '"':
            j = i + 1
            while j < n:
                if src[j] == "\\":
                    j += 2
                    continue
                if src[j] == '"':
                    j += 1
                    break
                j += 1
            blank(i, j)
            i = j
        elif c == "'":
            # char literal vs lifetime: a char literal closes with `'` within a
            # couple of characters and a lifetime never does.
            j = i + 1
            if j < n and src[j] == "\\":
                j += 2
                while j < n and src[j] != "'":
                    j += 1
                j = min(j + 1, n)
                blank(i, j)
                i = j
            elif j + 1 < n and src[j + 1] == "'":
                blank(i, j + 2)
                i = j + 2
            else:
                i += 1
        else:
            i += 1
    return "".join(out)


def literal_span(masked, start):
    """Bracket-match the array literal that opens at `masked[start] == '['`.

    Returns the index just past its `]`, or None if unterminated.
    """
    depth, i, n = 0, start, len(masked)
    while i < n:
        c = masked[i]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return None


def split_entries(masked, body_start, body_end):
    """Split `[body_start, body_end)` on TOP-LEVEL commas.

    Returns a list of (start, end) offsets, one per entry, dropping the empty
    tail that a trailing comma produces.
    """
    entries, depth, start = [], 0, body_start
    for i in range(body_start, body_end):
        c = masked[i]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif c == "," and depth == 0:
            entries.append((start, i))
            start = i + 1
    entries.append((start, body_end))
    return [(a, b) for (a, b) in entries if masked[a:b].strip()]


def sites(masked):
    """Yield every pinned-array definition site: (type_match, open, end)."""
    for m in ARRAY_TYPE.finditer(masked):
        j = m.end()
        while j < len(masked) and masked[j] in _BRIDGE:
            j += 1
        if j >= len(masked) or masked[j] != "[":
            continue
        end = literal_span(masked, j)
        if end is None:
            continue
        yield m, j, end


def recount(path, check_only):
    src = open(path).read()
    masked = mask(src)
    found = list(sites(masked))
    if not found:
        print(f"{path}: no pinned inventory array found", file=sys.stderr)
        return 2

    rc = 0
    edits = []
    for m, open_i, end_i in found:
        entries = split_entries(masked, open_i + 1, end_i - 1)
        counted = len(entries)
        declared = int(m.group("n"))
        # Measured on the MASKED text, not on `src`: an entry preceded by a
        # `//` comment block spans several lines of SOURCE while its own code
        # is one line, and calling that "wrapped" makes the diagnostic lie
        # about the failure it exists to name (`int_prelude_tests.rs`'s
        # `derived_lemmas` reported wrapped=1 for exactly this reason).
        single = sum(1 for a, b in entries if "\n" not in masked[a:b].strip())
        wrapped = counted - single
        elem = m.group("elem")
        line = src.count("\n", 0, m.start()) + 1
        print(
            f"{path}:{line}: [{elem}] declared={declared} counted={counted} "
            f"(single={single} wrapped={wrapped})"
        )
        if declared == counted:
            continue
        rc = 1
        print(f"{path}:{line}: PIN WRONG -- declared {declared}, counted {counted}")
        if not check_only:
            edits.append((m.start("n"), m.end("n"), str(counted), declared, line))

    # Rewrite back-to-front so earlier offsets stay valid.
    for a, b, new, declared, line in reversed(edits):
        src = src[:a] + new + src[b:]
        print(f"{path}:{line}: REWROTE {declared} -> {new}")
    if edits:
        open(path, "w").write(src)
    return rc


def main():
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
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
