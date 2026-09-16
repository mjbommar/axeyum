#!/usr/bin/env python3
import csv, os, sys

csv.field_size_limit(200_000_000)
SEP = "\\p"
W1 = "a datatype field sort with no expansion variable"
ARR = "outside the current Bool/Int lazy array route"

for path in sys.argv[1:]:
    with open(path, newline="") as fh:
        rows = list(csv.DictReader(fh, delimiter="\t"))
    print(f"### {os.path.basename(path)}")
    for r in rows:
        if r["verdict"] != "unknown":
            continue
        d = [x for x in (r.get("decline_details") or "").split(SEP) if x.strip()]
        t = d[-1] if d else ""
        tag = None
        if W1 in t:
            tag = "W1-TERMINAL"
        elif ARR in t:
            tag = "ARRAY-NONBV-TERMINAL"
        elif any(W1 in x for x in d):
            tag = "W1-in-trail"
        if tag:
            print(f"  {tag:22s} {os.path.basename(r['corpus_path'])}")
    print()
