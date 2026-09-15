#!/usr/bin/env python3
"""LEMMA-INPUT -- R8: show the control is NOT VACUOUS.

ADR-2075 could not establish this for its own lever and said so: on a DECIDED
row the solver's soft deadline wins, the breadcrumb never prints, and the phase
reading that would show the changed code executing is unavailable.

This lane has a probe that works there, because the attribution instrument
reports on a wall-clock thread rather than at the watchdog: a decided control
row that carries `calls>0` is a row the initial-lemma refresh RAN on.  That is
the changed code, entered, on a row whose verdict must not move.

Exit status depends on the finding (a control shown vacuous exits non-zero).
"""

import pathlib
import sys

ATTR = pathlib.Path(sys.argv[1])
DECIDED = pathlib.Path(sys.argv[2])

decided = {ln.strip() for ln in DECIDED.read_text().splitlines() if ln.strip()}
ran = []
noread = []
zero = []
for line in ATTR.read_text().splitlines():
    if not line.strip():
        continue
    parts = line.split("\t")
    name, verdict, stats = parts[0], parts[1], parts[4]
    if name not in decided:
        continue
    if stats.strip() == "NOREAD":
        noread.append(name)
        continue
    fields = dict(
        (tok.split("=", 1)[0], int(tok.split("=", 1)[1]))
        for tok in stats.split()
        if "=" in tok and tok.split("=", 1)[1].lstrip("-").isdigit()
    )
    (ran if fields.get("calls", 0) > 0 else zero).append((name, fields.get("calls", 0)))

print(f"control rows (decided in the census): {len(decided)}")
print(f"  with a reading AND calls>0 -- the refresh RAN there: {len(ran)}")
print(f"  with a reading but calls==0 -- the refresh never ran:  {len(zero)}")
print(f"  NOREAD (finished inside the instrument's 1 s period): {len(noread)}")
print()
for name, calls in sorted(ran, key=lambda r: -r[1])[:10]:
    print(f"  calls={calls}\t{name}")

if not ran:
    print()
    print("FINDING: the control is VACUOUS -- the changed code runs on none of it.")
    sys.exit(1)
print()
print("NON-VACUOUS: the route binding these rows is "
      "`euf::check_with_incremental_arith` -> `IncrementalArithDpll::"
      "{new_within,assert_incremental}` -> `refresh_initial_lemmas`, and the "
      "call counter above is that function being entered.")
