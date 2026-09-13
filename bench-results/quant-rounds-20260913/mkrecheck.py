#!/usr/bin/env python3
"""The rows that did NOT come back `SHAPE`, for an independent re-run.

At a 24 s budget roughly 1-1.5 % of files flip on ambient load alone, and the
five `OTHER` rows in this lane's exit census carry a give-up string that is not
the loop's at all (an earlier rung's timeout printed first).  A single pairing
is not a finding, so every non-`SHAPE` row is re-run and both the raw and the
re-checked classification are published.

Writes pop/recheck.txt.
"""

import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"


def main() -> int:
    out = HERE / "pop"
    out.mkdir(exist_ok=True)
    rows: list[str] = []
    seen = 0
    for tsv in sorted((HERE / "out").glob("exit-*.tsv")):
        lines = tsv.read_text().splitlines()
        head = lines[0].split("\t")
        fi, ki = head.index("file"), head.index("exit_kind")
        for ln in lines[1:]:
            cols = ln.split("\t")
            if len(cols) <= ki:
                continue
            seen += 1
            if cols[ki] != "SHAPE":
                rows.append(CORPUS + cols[fi])
    if not seen:
        print("ABORT: no exit-*.tsv rows -- the recheck list would be a false EMPTY",
              file=sys.stderr)
        return 2
    (out / "recheck.txt").write_text("".join(r + "\n" for r in rows))
    print(f"{len(rows)} non-SHAPE rows of {seen}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
