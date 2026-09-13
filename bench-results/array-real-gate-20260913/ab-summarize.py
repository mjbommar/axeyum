#!/usr/bin/env python3
"""Summarize the interleaved A/B, and FAIL on any finding that matters.

Exit status depends on the finding, because a summarizer that always exits 0
turns a wrong verdict into a table row:

* exit 3 — a `sat`/`unsat` contradicting the file's declared `:status`, in
  either arm. This is the wrong-verdict check and it is the reason to run it.
* exit 4 — the two arms return OPPOSITE decisions on one file (one says `sat`,
  the other `unsat`). At most one of them can be right.
* exit 2 — an empty or unreadable run. An empty sweep is not a clean sweep.

A row where one arm decides and the other says `unknown` is a MOVE, not a
disagreement: report it, do not fail on it.

Usage: ab-summarize.py <tsv>...
"""
import sys


def read(path):
    with open(path) as f:
        head = f.readline().rstrip("\n").split("\t")
        rows = [dict(zip(head, line.rstrip("\n").split("\t"))) for line in f if line.strip()]
    return head, rows


def main(argv):
    if not argv:
        print("usage: ab-summarize.py <tsv>...", file=sys.stderr)
        return 2
    bad_status = []
    opposite = []
    total_rows = 0
    print(
        f"{'division':<12}{'n':>5}{'A dec':>7}{'B dec':>7}{'delta':>7}"
        f"{'B-only':>8}{'A-only':>8}"
    )
    for path in argv:
        head, rows = read(path)
        if not rows:
            print(f"ABORT: {path} has no rows", file=sys.stderr)
            return 2
        for col in ("axeyum", "axeyumb", "status"):
            if col not in head:
                print(f"ABORT: {path} has no `{col}` column", file=sys.stderr)
                return 2
        total_rows += len(rows)
        a_dec = b_dec = b_only = a_only = 0
        for r in rows:
            a, b, st = r["axeyum"], r["axeyumb"], r["status"]
            for arm, v in (("A", a), ("B", b)):
                if v in ("sat", "unsat") and st in ("sat", "unsat") and v != st:
                    bad_status.append((path, r["file"], arm, v, st))
            if {a, b} == {"sat", "unsat"}:
                opposite.append((path, r["file"], a, b))
            a_dec += a in ("sat", "unsat")
            b_dec += b in ("sat", "unsat")
            b_only += b in ("sat", "unsat") and a == "unknown"
            a_only += a in ("sat", "unsat") and b == "unknown"
        name = path.rsplit("/", 1)[-1].replace(".tsv", "")
        print(
            f"{name:<12}{len(rows):>5}{a_dec:>7}{b_dec:>7}{b_dec - a_dec:>+7}"
            f"{b_only:>8}{a_only:>8}"
        )
    print(f"rows: {total_rows}")

    if bad_status:
        print(f"\nWRONG VERDICT vs declared :status ({len(bad_status)}):")
        for path, f, arm, v, st in bad_status:
            print(f"  {path} {f} arm={arm} got={v} declared={st}")
        return 3
    print("no verdict contradicts a declared :status")
    if opposite:
        print(f"\nARMS DISAGREE ({len(opposite)}):")
        for path, f, a, b in opposite:
            print(f"  {path} {f} A={a} B={b}")
        return 4
    print("no file where the two arms decide in opposite directions")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
