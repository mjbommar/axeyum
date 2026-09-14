#!/usr/bin/env python3
"""Rows that STILL abort with the memory limit set.

The admission screens are supposed to make an abort impossible once the solver
knows its budget.  Any row that aborts in the ARM is an allocation no screen
prices -- the residual, and the thing a follow-up has to find.
"""
import sys

for path in sys.argv[1:]:
    with open(path) as fh:
        head = fh.readline().rstrip("\n").split("\t")
        for line in fh:
            r = dict(zip(head, line.rstrip("\n").split("\t")))
            if r["arm_rc"] == "134":
                print(f"{r['arm_ms']:>7}ms  base_rc={r['base_rc']} "
                      f"{r['file'].split('non-incremental/')[-1]}")
