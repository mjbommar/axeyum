#!/usr/bin/env python3
"""Print the corpus paths of census rows matching a bucket substring."""
import sys

CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"
want = sys.argv[2]
probe = sys.argv[3] if len(sys.argv) > 3 else None
with open(sys.argv[1]) as fh:
    head = fh.readline().rstrip("\n").split("\t")
    for line in fh:
        r = dict(zip(head, line.rstrip("\n").split("\t")))
        if want in r["bucket"] and (probe is None or r["online_probe"] == probe):
            print(CORPUS + r["file"])
