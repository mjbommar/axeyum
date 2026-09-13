"""Check that the three artifacts for each division actually agree.

A board TSV, a winnable list and a census are three files that can drift apart
silently.  Every number this lane publishes is a ratio between two of them --
"185 of 187 winnable rows", "17 of 17" -- so a mismatch would not produce an
error, it would produce a WRONG RATIO that still looks like a measurement.

Five properties, each checkable and each able to fail:

  1. The board TSV has exactly the pinned 200 rows, in pinned-list order.
  2. `winnable/<DIV>.txt` is EXACTLY the rows where we said neither `sat` nor
     `unsat` and at least one reference said one of them -- recomputed here from
     the board, not read from the file and trusted.
  3. `census/<DIV>.tsv` covers the winnable set exactly: no missing row (which
     would shrink a denominator) and no extra row (which would mean the census
     ran over something else).
  4. Census and board agree about the same file: a census row that came back
     `sat`/`unsat` contradicts the board row that called it winnable.  These are
     two runs of the same binary at the same budget, so a disagreement is real
     information -- nondeterminism, or contention -- and must not be silent.
  5. Every row of the board records an outcome for all three solvers, and the
     measurement wall (`wrapper-killed`) is reported rather than assumed absent.

Exit 1 on any violation, so this can gate.

Run from this directory:  python3 check-artifact-integrity.py
"""

import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
LISTS = HERE.parent / "parity-lists"
CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"
DIVS = ["AUFLIRA", "UFNIA", "ABV", "ALIA", "AUFNIRA", "AUFBV", "FP"]
STEM = {"FP": "FP-fullspan"}
DECIDED = {"sat", "unsat"}


def tsv(p):
    lines = p.read_text().rstrip("\n").split("\n")
    head = lines[0].split("\t")
    return [dict(zip(head, ln.split("\t"))) for ln in lines[1:]]


def main():
    bad = 0
    ran = 0
    for div in DIVS:
        bp = HERE / f"{div}.tsv"
        if not bp.exists():
            print(f"{div:9s} board DID NOT RUN")
            continue
        ran += 1
        rows = tsv(bp)
        errs = []

        # 1. exactly the pinned 200, in order
        lp = LISTS / f"{STEM.get(div, div)}.txt"
        got = [r["file"] for r in rows]
        if not lp.exists():
            # An absent pinned list is the one input that makes every other
            # check meaningless, so it is NAMED rather than raised.  A traceback
            # is an exit status with no finding in it.
            errs.append(f"pinned list {lp} is ABSENT -- cannot check the board")
            pinned = None
        else:
            pinned = [
                ln[len(CORPUS):]
                for ln in lp.read_text().rstrip("\n").split("\n")
            ]
            if got != pinned:
                errs.append(f"board is not the pinned list in order "
                            f"({len(got)} rows vs {len(pinned)} pinned)")

        # 2. winnable recomputed, not trusted
        recomputed = [
            r["file"] for r in rows
            if r["axeyum"] not in DECIDED
            and (r["z3"] in DECIDED or r["cvc5"] in DECIDED)
        ]
        wp = HERE / "winnable" / f"{div}.txt"
        if not wp.exists():
            errs.append("winnable list is ABSENT")
            stored = None
        else:
            stored = [
                ln[len(CORPUS):] for ln in wp.read_text().split("\n") if ln
            ]
            if stored != recomputed:
                errs.append(f"winnable list disagrees with the board "
                            f"(file {len(stored)}, recomputed {len(recomputed)})")

        # 3 + 4. census covers the winnable set exactly, and agrees with it
        cp = HERE / "census" / f"{div}.tsv"
        if cp.exists():
            crows = tsv(cp)
            ckeys = [r["file"] for r in crows]
            if ckeys != recomputed:
                miss = [f for f in recomputed if f not in set(ckeys)]
                extra = [f for f in ckeys if f not in set(recomputed)]
                errs.append(f"census does not cover the winnable set "
                            f"(missing {len(miss)}, extra {len(extra)})")
            decided_again = [
                r["file"] for r in crows if r["verdict"] in DECIDED
            ]
            if decided_again:
                errs.append(f"{len(decided_again)} census row(s) DECIDED a file "
                            f"the board called winnable, e.g. {decided_again[0]}")
        elif recomputed:
            errs.append(f"census DID NOT RUN over {len(recomputed)} winnable rows")

        # 5. every row has an outcome for all three solvers
        for s in ("ax", "z3", "cvc5"):
            blank = sum(1 for r in rows if not r.get(f"{s}_k"))
            if blank:
                errs.append(f"{blank} row(s) have no {s} outcome recorded")
        kills = {
            s: sum(1 for r in rows if r[f"{s}_k"] == "wrapper-killed")
            for s in ("ax", "z3", "cvc5")
        }

        wall = sum(kills.values())
        note = f"measurement wall hit {wall} time(s)" if wall else "measurement wall never hit"
        if errs:
            bad += 1
            print(f"{div:9s} !! {len(errs)} problem(s); {note}")
            for e in errs:
                print(f"          - {e}")
        else:
            print(f"{div:9s} OK  200 rows, winnable {len(recomputed)} recomputed"
                  f" and matching, census "
                  f"{'covers it exactly' if cp.exists() else 'not needed (0 winnable)' if not recomputed else 'DID NOT RUN'}"
                  f"; {note}")

    if ran == 0:
        print("\nNO BOARD RAN -- this is not a clean result")
        return 1
    print(f"\n{ran} division(s) checked, {bad} with problems")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
