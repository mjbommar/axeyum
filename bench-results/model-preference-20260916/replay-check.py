#!/usr/bin/env python3
"""Independently replay every arm-B `sat` of the ADR-2140 A/B through the
Python binding: `smt.solve(text, model_preference="zero").replay()`.

A `sat` printed by `smtcomp_cli` has already replayed inside `SatBvBackend`,
so this is a SECOND, independent pass over the same files on a different host
with the same policy. It prints `REPLAY|sat=N|replayed=R|failed=F|undecided=U`
and exits 1 if any replay returned False.

Usage: replay-check.py half1.tsv half2.tsv [timeout_ms]
"""

from __future__ import annotations

import csv
import sys

from axeyum import smt

CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"
timeout_ms = int(sys.argv[-1]) if sys.argv[-1].isdigit() else 24_000
paths = [p for p in sys.argv[1:] if p.endswith(".tsv")]

rows = []
for path in paths:
    with open(path, newline="") as fh:
        rows.extend(r for r in csv.DictReader(fh, delimiter="\t") if r["B"] == "sat")

replayed = failed = undecided = 0
for r in rows:
    with open(CORPUS + r["file"]) as fh:
        text = fh.read()
    out = smt.solve(text, timeout_ms=timeout_ms, model_preference="zero")
    if out.status != "sat":
        undecided += 1
        continue
    if out.replay_available and out.replay():
        replayed += 1
    else:
        failed += 1
        print(f"REPLAY-FAILED {r['file']} replay_available={out.replay_available}")
print(f"REPLAY|sat={len(rows)}|replayed={replayed}|failed={failed}|undecided={undecided}")
sys.exit(1 if failed else 0)
