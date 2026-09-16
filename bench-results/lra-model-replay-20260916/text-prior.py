#!/usr/bin/env python3
"""Text-level prior over the pinned QF_LRA 200: which constructs even APPEAR.

This is a PRIOR, not the finding -- it counts tokens in the raw SMT-LIB before
parsing and rewriting, so it is an upper bound on what reaches the online
engine. Its job is to be a cross-check on the census histogram: a construct the
census names as dominant had better appear here, and a construct that appears
in zero files cannot be the answer.
"""

import collections
import pathlib
import re
import sys

CORPUS = pathlib.Path(
    "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental"
)
listfile = pathlib.Path(sys.argv[1])

PATTERNS = {
    "ite": re.compile(r"\(\s*ite\b"),
    "div-slash": re.compile(r"\(\s*/\s"),
    "distinct": re.compile(r"\(\s*distinct\b"),
    "not-eq": re.compile(r"\(\s*not\s*\(\s*=\s"),
    "to_real": re.compile(r"\(\s*to_real\b"),
    "to_int": re.compile(r"\(\s*to_int\b"),
    "is_int": re.compile(r"\(\s*is_int\b"),
    "bare-eq": re.compile(r"\(\s*=\s"),
    "declare-fun-arity>0": re.compile(r"\(declare-fun\s+\S+\s*\(\s*[^)\s]"),
}

files_with = collections.Counter()
occurrences = collections.Counter()
n = 0
for rel in listfile.read_text().split():
    p = CORPUS / rel
    try:
        text = p.read_text(errors="replace")
    except OSError:
        continue
    n += 1
    for name, rx in PATTERNS.items():
        hits = len(rx.findall(text))
        if hits:
            files_with[name] += 1
            occurrences[name] += hits

print(f"files scanned: {n}")
print(f"{'construct':24s} {'files':>6s} {'occurrences':>12s}")
for name in PATTERNS:
    print(f"{name:24s} {files_with[name]:6d} {occurrences[name]:12d}")
