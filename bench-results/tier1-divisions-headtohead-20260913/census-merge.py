"""Merge each division's census shards into census/<DIV>.tsv, in winnable order.

ABORTS if the shards together do not cover the winnable set exactly.  A short
shard must not silently become a smaller census denominator -- the census
denominator IS the claim ("the WHOLE winnable set, not a sample"), so a merge
that quietly drops rows would turn the one thing this artifact promises into a
sample without saying so.
"""

import pathlib
import sys

LANE = pathlib.Path(__file__).resolve().parent
SRC = pathlib.Path("/nas3/data/axeyum/harness/tier1-divisions/census")
CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"
DIVS = ["AUFLIRA", "UFNIA", "ABV", "ALIA", "AUFNIRA", "AUFBV", "FP"]


def main():
    rc = 0
    for div in DIVS:
        wf = LANE / "winnable" / f"{div}.txt"
        if not wf.exists():
            print(f"SKIP {div}: no winnable list (board did not run)")
            rc = 1
            continue
        want = [
            ln[len(CORPUS):]
            for ln in wf.read_text().split("\n")
            if ln
        ]
        # An EMPTY winnable set is a RESULT -- it means every file a reference
        # decided, we decided too -- and it must not render as "census DID NOT
        # RUN", which is the absence of a measurement.  Without this branch the
        # two are indistinguishable in the output, because both produce zero
        # census rows.
        if not want:
            print(f"{div}: winnable set is EMPTY -- nothing to census"
                  f" (a result about the division, not a missing step)")
            continue
        parts = [SRC / f"{div}.{s}.tsv" for s in ("s0", "s1")]
        parts += [SRC / f"{div}.tsv"]
        head, seen = None, {}
        for p in parts:
            if not p.exists():
                continue
            lines = p.read_text().rstrip("\n").split("\n")
            head = lines[0]
            for ln in lines[1:]:
                k = ln.split("\t")[0]
                if k in seen:
                    print(f"ABORT {div}: duplicate row key {k}")
                    return 2
                seen[k] = ln
        if head is None:
            print(f"{div}: census DID NOT RUN (no shard files)")
            rc = 1
            continue
        missing = [f for f in want if f not in seen]
        extra = [k for k in seen if k not in want]
        if missing or extra:
            print(f"INCOMPLETE {div}: have {len(seen)} of {len(want)}; "
                  f"missing {len(missing)} extra {len(extra)}")
            rc = 1
            continue
        (LANE / "census").mkdir(exist_ok=True)
        (LANE / "census" / f"{div}.tsv").write_text(
            head + "\n" + "".join(seen[f] + "\n" for f in want)
        )
        print(f"CENSUS-MERGED {div}: {len(want)} rows")
    return rc


if __name__ == "__main__":
    sys.exit(main())
