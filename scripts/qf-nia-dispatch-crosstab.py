#!/usr/bin/env python3
"""Cross-tab the honest cause against who consumed the budget, and against the
declared :status.  A cause tells you what refused; `bound_by` tells you what
spent the clock, and they are different questions."""
import collections
import csv
import os
import re
import sys

import importlib.util as _ilu
_spec = _ilu.spec_from_file_location(
    "qf_nia_dispatch_classify",
    os.path.join(os.path.dirname(os.path.abspath(__file__)),
                 "qf-nia-dispatch-classify.py"))
_mod = _ilu.module_from_spec(_spec)
_spec.loader.exec_module(_mod)
decompose = _mod.decompose

import subprocess as _sp
ROOT = _sp.run(["git", "rev-parse", "--show-toplevel"],
               capture_output=True, text=True,
               cwd=os.path.dirname(os.path.abspath(__file__))).stdout.strip()
STATUS_RE = re.compile(r"\(\s*set-info\s+:status\s+(sat|unsat|unknown)\s*\)")

rows = list(csv.DictReader(open(sys.argv[1]), delimiter="\t"))
short = {
    "integer bit-blast width ladder: wall-clock timeout reached": "ladder-clock",
    "estimated N CNF clauses before lowering exceeds budget N (oversized encoding refused gracefully)": "cnf-budget",
    "bounded integer model overflowed at width N (assertion #N is false over exact semantics); widen the bound": "replay-overflow",
    "watchdog fired before the worker thread returned": "watchdog",
    "combined-theory timeout after scalar backend": "scalar-clock",
    "integer constant N does not fit the bounded width N; widen the bound": "const-width",
    "no model within the bounded integer width N; widen the bound": "in-range-unsat",
}


def label(h):
    for k, v in short.items():
        if h.startswith(k[:60]):
            return v
    return h[:40]


tab = collections.Counter()
stat = collections.Counter()
att = collections.defaultdict(list)
for r in rows:
    _o, h, _k = decompose(r)
    c = label(h)
    tab[(c, r["bound_by"])] += 1
    m = STATUS_RE.search(open(r["file"], errors="replace").read())
    stat[(c, m.group(1) if m else "none")] += 1
    att[c].append(int(r["attempts"]))

print("| honest cause | bound_by | files |")
print("|---|---|---:|")
for (c, b), n in sorted(tab.items(), key=lambda kv: -kv[1]):
    print(f"| {c} | {b} | {n} |")
print()
print("| honest cause | declared :status | files |")
print("|---|---|---:|")
for (c, s), n in sorted(stat.items(), key=lambda kv: -kv[1]):
    print(f"| {c} | {s} | {n} |")
print()
print("| honest cause | attempts min..max | files |")
print("|---|---|---:|")
for c, a in sorted(att.items(), key=lambda kv: -len(kv[1])):
    print(f"| {c} | {min(a)}..{max(a)} | {len(a)} |")

# per-class file lists for follow-up
outdir = sys.argv[2] if len(sys.argv) > 2 else None
if outdir:
    os.makedirs(outdir, exist_ok=True)
    byclass = collections.defaultdict(list)
    for r in rows:
        _o, h, _k = decompose(r)
        byclass[label(h)].append(r["file"])
    for c, fs in byclass.items():
        p = os.path.join(outdir, f"class-{c}.txt")
        with open(p, "w") as fh:
            fh.write("\n".join(sorted(fs)) + "\n")
        print("wrote", p, len(fs))
