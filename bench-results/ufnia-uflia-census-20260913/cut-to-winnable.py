"""Cut each division's full-200 run down to its WINNABLE rows.

The census denominator is the winnable set -- every file where we returned
`unknown` and a reference decided -- not the whole pinned 200.  One pass over
the 200 produced both the board row and the census row for each file, so this
is a projection, not a second measurement.

ABORTS if a winnable file has no row: that would shrink the census denominator
silently, which is the whole failure class `merge-division.py` also guards.
"""

import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent


def main() -> int:
    seen = 0
    for div in ("UFNIA", "UFLIA"):
        census = HERE / "census" / f"{div}.tsv"
        winnable = HERE / "winnable" / f"{div}.txt"
        if not (census.exists() and winnable.exists()):
            print(f"{div}: DID NOT RUN")
            continue
        seen += 1
        want = [l.strip() for l in winnable.read_text().split("\n") if l.strip()]
        lines = census.read_text().rstrip("\n").split("\n")
        rows = {ln.split("\t")[0]: ln for ln in lines[1:]}
        missing = [f for f in want if f not in rows]
        if missing:
            print(f"ABORT {div}: {len(missing)} winnable files have no census row,"
                  f" e.g. {missing[:2]}")
            return 2
        out = HERE / "census" / f"{div}.winnable.tsv"
        out.write_text(lines[0] + "\n" + "".join(rows[f] + "\n" for f in want))
        print(f"CUT-OK {div}: {len(want)} winnable rows of {len(lines) - 1} measured")
    return 0 if seen else 1


if __name__ == "__main__":
    sys.exit(main())
