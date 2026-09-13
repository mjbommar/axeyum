"""Rank the blocker census -- under ADR-1936, which forbids ranking most of it.

Run from this directory:  python3 census-summarize.py

ADR-1936: a row whose dispatch did not reach the end of the ladder is
UNCLASSIFIED and is NEVER reported by its give-up reason.  So this script does
two things in order:

  1. Print the `attempts=` distribution, and the ladder length taken as the
     MAXIMUM attempts observed on any row of the division.  That maximum is the
     empirical answer to "how long is this division's ladder when it completes";
     it is a lower bound on the true length, which makes the UNCLASSIFIED count
     a lower bound too -- the conservative direction.
  2. Rank give-up reasons over the CLASSIFIED rows only, and report the
     UNCLASSIFIED rows separately, broken out by the rung they stopped at.
"""

import collections
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
DIVS = ["QF_ABVFP", "QF_BVFP", "QF_UFBV"]


def rows(div):
    p = HERE / "census" / f"{div}.tsv"
    if not p.exists():
        return None
    lines = p.read_text().rstrip("\n").split("\n")
    head = lines[0].split("\t")
    return [dict(zip(head, ln.split("\t"))) for ln in lines[1:]]


def bucket(g):
    """Collapse a give-up detail to a reason, keeping enough to act on."""
    if g in ("none", ""):
        return "(no give-up line)"
    m = re.match(r"give-up kind=(\S+) detail=(.*)", g)
    if not m:
        return g[:90]
    kind, detail = m.group(1), m.group(2)
    return f"{kind}: {detail[:110]}"


def main():
    any_seen = False
    for div in DIVS:
        rs = rows(div)
        if rs is None:
            print(f"== {div}: census DID NOT RUN")
            continue
        any_seen = True
        n = len(rs)
        att = collections.Counter(r["attempts"] for r in rs)
        numeric = [int(r["attempts"]) for r in rs if r["attempts"].isdigit()]
        ladder = max(numeric) if numeric else 0

        print(f"== {div}  census rows={n}  ladder(empirical max attempts)={ladder}")
        print(f"   attempts distribution: {dict(sorted(att.items(), key=str))}")
        print(
            f"   wrapper-killed rc=124: "
            f"{sum(r['rc'] == '124' for r in rs)}   rc134: "
            f"{sum(r['rc'] == '134' for r in rs)}"
        )

        classified, unclassified, noroute = [], [], []
        for r in rs:
            a = r["attempts"]
            if not a.isdigit():
                noroute.append(r)
            elif int(a) < ladder:
                unclassified.append(r)
            else:
                classified.append(r)

        # A file we actually decided on the census re-run is not a blocker row.
        decided = [r for r in classified if r["verdict"] in ("sat", "unsat")]
        classified = [r for r in classified if r["verdict"] not in ("sat", "unsat")]

        print(
            f"   CLASSIFIED {len(classified)}   UNCLASSIFIED {len(unclassified)}"
            f"   no-route {len(noroute)}   decided-on-recheck {len(decided)}"
        )

        print("   -- classified give-up reasons (rankable):")
        for g, c in collections.Counter(bucket(r["giveup"]) for r in classified).most_common():
            print(f"      {c:4d}  {g}")

        if unclassified:
            print("   -- UNCLASSIFIED: dispatch stopped early. NOT rankable by reason.")
            print("      broken out by the rung it stopped at (last=):")
            for k, c in collections.Counter(
                (r["attempts"], r["last"]) for r in unclassified
            ).most_common():
                print(f"      {c:4d}  attempts={k[0]} last={k[1]}")
            if "open_after" in unclassified[0]:
                print(
                    "      and by the OPEN SEGMENT (after= names the last rung that"
                    " recorded; the budget went into what ran next and never"
                    " reported):"
                )
                for k, c in collections.Counter(
                    (r["open_after"], r["deepest"]) for r in unclassified
                ).most_common():
                    print(f"      {c:4d}  open_after={k[0]} deepest={k[1]}")
        if noroute:
            print(f"   -- no route trail at all: {len(noroute)} (own row, not an absence)")
            for k, c in collections.Counter(r["rc"] for r in noroute).most_common():
                print(f"      {c:4d}  rc={k}")
        print()
    return 0 if any_seen else 1


if __name__ == "__main__":
    sys.exit(main())
