#!/usr/bin/env python3
"""Hit rate of the routes ADR-1966 changed, per pinned division list.

A control division is only a control if it EXERCISES the changed route without
refusing.  A division that structurally cannot reach the route proves nothing
about cost, and two lanes this week shipped exactly that kind of empty control
(`ufbv_online` on 0 of 400; `q:egraph` on 0 of 200).  So this reports, per
division, how many files carry the shape each fixed site needs:

  array_valued_uf   -- `(declare-fun f (..) (Array ..))`, the declaration whose
                       eager-Ackermann refusal names the route below it.
  arith_uf          -- an arithmetic-sorted `declare-fun` with arguments, the
                       gate (`has_arithmetic_function`) on the rung that
                       refuses.
  both              -- files that can reach the refusal at all.
  datatype          -- `declare-datatypes`, the gate on the datatype rung.
  datatype_arr_uf_field
                    -- a datatype whose declaration mentions `Array` or a
                       declared sort, the refusal ADR-1927's census named.

This is a STRUCTURAL upper bound read off the text, not a trace: a file counted
here may still be decided before the rung runs.  It is used to aim the A/B and
to show a control is non-empty, never to claim a file count.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

DECL_FUN = re.compile(r"\(\s*declare-fun\s+(\S+)\s*\(([^)]*)\)\s*(.*)")
ARRAY_RET = re.compile(r"^\s*\(\s*Array\b")
ARITH_RET = re.compile(r"^\s*(Int|Real)\b")


def classify(text: str) -> dict[str, bool]:
    array_valued_uf = False
    arith_uf = False
    for m in DECL_FUN.finditer(text):
        args, ret = m.group(2).strip(), m.group(3)
        if not args:
            continue  # a constant, not an applied function
        if ARRAY_RET.match(ret):
            array_valued_uf = True
        if ARITH_RET.match(ret):
            arith_uf = True
    dt = "declare-datatypes" in text or "declare-datatype " in text
    dt_field = False
    if dt:
        for m in re.finditer(r"\(\s*declare-datatypes?\b", text):
            chunk = text[m.start() : m.start() + 4000]
            if "Array" in chunk:
                dt_field = True
                break
    return {
        "array_valued_uf": array_valued_uf,
        "arith_uf": arith_uf,
        "both": array_valued_uf and arith_uf,
        "datatype": dt,
        "datatype_arr_field": dt_field,
    }


def main() -> int:
    lists = sys.argv[1:]
    if not lists:
        print("usage: hit-rate.py <pinned-list>...", file=sys.stderr)
        return 2
    keys = ["array_valued_uf", "arith_uf", "both", "datatype", "datatype_arr_field"]
    print(f"{'division':<14}{'files':>6}" + "".join(f"{k:>22}" for k in keys))
    for lp in lists:
        p = Path(lp)
        files = [ln.strip() for ln in p.read_text().splitlines() if ln.strip()]
        counts = dict.fromkeys(keys, 0)
        read = 0
        for f in files:
            try:
                text = Path(f).read_text(errors="replace")
            except OSError:
                continue
            read += 1
            for k, v in classify(text).items():
                counts[k] += int(v)
        if read == 0:
            print(f"{p.stem:<14}{0:>6}  NO FILE READ -- the measurement never "
                  f"reached its subject")
            continue
        print(
            f"{p.stem:<14}{read:>6}"
            + "".join(f"{counts[k]:>22}" for k in keys)
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
