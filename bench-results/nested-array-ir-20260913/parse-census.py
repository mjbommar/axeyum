#!/usr/bin/env python3
"""The parse-gate census over WHOLE divisions, not a sample.

`parse_rate` prints `ok <bytes> <path>` / `err <reason> <path>` per file. This
runs it over every `.smt2` file of the named divisions and histograms the
reasons, so the count attributed to `nested array element sort is unsupported`
is the exact population count rather than an n=2 extrapolation.

The point of doing this over the whole division rather than the pinned 200 is
that the pinned 200 is for the A/B; this is for the DENOMINATOR, and a
denominator derived from a sample is what
`bench-results/session-20260911-smtlib/coverage/blockmap.txt` did wrong.

Usage: parse-census.py <parse_rate-binary> <out-dir> <division>...
"""
import collections
import os
import re
import subprocess
import sys

ROOT = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental"

# `parse_rate` prints `format!("{e:?}")` truncated to 200 chars, and an
# `Unsupported` reason embeds the offending SExpr's Debug — so the raw string is
# unique per file and a naive histogram has one bucket per file. Normalising is
# therefore not cosmetic: without it the census cannot count anything. The
# grouping key is the human-written prefix of the reason, up to the first place
# a term or sort gets interpolated.
_CUT = re.compile(r'(List\(|Atom\(|\{|\[)')


def normalise(reason):
    """Collapse an interpolated parse-error message to its constant prefix."""
    m = _CUT.search(reason)
    if m:
        reason = reason[: m.start()]
    return reason.rstrip(' :"\\').strip()


def main():
    binary = sys.argv[1]
    outdir = sys.argv[2]
    divisions = sys.argv[3:]
    os.makedirs(outdir, exist_ok=True)
    for div in divisions:
        files = []
        for dirpath, _, fnames in os.walk(os.path.join(ROOT, div)):
            for fn in fnames:
                if fn.endswith(".smt2"):
                    files.append(os.path.join(dirpath, fn))
        files.sort()
        listfile = os.path.join(outdir, f"{div}.all.txt")
        with open(listfile, "w") as f:
            f.write("\n".join(files) + "\n")
        raw = os.path.join(outdir, f"{div}.parse.txt")
        with open(raw, "w") as out:
            # parse_rate exits non-zero when any file fails, which is the norm
            # here, so the exit status is NOT the finding; the lines are.
            subprocess.run([binary, listfile], stdout=out, stderr=subprocess.STDOUT)
        ok = 0
        hist = collections.Counter()
        nested = []
        with open(raw) as f:
            for line in f:
                if line.startswith("ok "):
                    ok += 1
                elif line.startswith("err "):
                    rest = line[4:].rstrip("\n")
                    # `err <reason-with-spaces> <path>`: the path is the last field
                    reason, _, path = rest.rpartition(" ")
                    hist[normalise(reason)] += 1
                    if "nested array" in reason:
                        nested.append(path)
        with open(os.path.join(outdir, f"{div}.nested.txt"), "w") as f:
            if nested:
                f.write("\n".join(nested) + "\n")
        total = ok + sum(hist.values())
        print(f"== {div}: {total} files, {ok} parse ok ({100.0 * ok / total:.1f}%)")
        for reason, n in hist.most_common(12):
            print(f"   {n:7d}  {100.0 * n / total:5.1f}%  {reason[:110]}")
        sys.stdout.flush()


main()
