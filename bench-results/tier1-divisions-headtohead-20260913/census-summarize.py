"""Rank the blocker census -- under ADR-1936 and ADR-1941, which forbid ranking
most of it, and ADR-1950, which forbids ranking a "budget" reason without
saying WHICH budget.

Run from this directory:  python3 census-summarize.py

ADR-1936: a row whose dispatch did not reach the end of the ladder is
UNCLASSIFIED and is NEVER reported by its give-up reason.
ADR-1941: `attempts=` alone cannot make that call -- the discriminator is the
`route-open` SEGMENT.  A row with no open segment finished ITS OWN ladder, which
may legitimately be shorter than the division's longest.  Both readings are
printed, as ADR-1941 step 6 requires.
ADR-1950: every ranked family carries min/median/max of budget REMAINING, so a
family labelled ROUND that actually burns the clock is reclassified by its own
data.
"""

import collections
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
DIVS = ["AUFLIRA", "UFNIA", "ABV", "ALIA", "AUFNIRA", "AUFBV", "FP"]
BUDGET_MS = 24_000


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
    # Normalise the MEASURED quantity out of the reason so rows aggregate, and
    # normalise the SORT EXPRESSION out of a parse refusal for the same reason:
    # `nested array element sort is unsupported: List([Atom("Array"), ...])`
    # prints a different term on every file and would rank as N rows of 1,
    # hiding that they are all one refusal.
    detail = re.sub(r"\bList\(\[.*", "<SORT>", detail)
    detail = re.sub(r"\b\d+\b", "N", detail)
    return f"{kind}: {detail[:110]}"


def ms_left(rs):
    out = []
    for r in rs:
        try:
            out.append(BUDGET_MS - int(r["total_ms"]))
        except (ValueError, KeyError):
            pass
    return sorted(out)


def magnitudes(rows_):
    out = []
    for r in rows_:
        m = re.search(r"has (\d+) (?:semantic atoms|DAG nodes)", r["giveup"])
        if m:
            out.append(int(m.group(1)))
    return sorted(out)


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
        strict_unclassified = 0  # the attempts=-only reading, published beside it
        for r in rs:
            a = r["attempts"]
            if not a.isdigit():
                noroute.append(r)
                continue
            if int(a) < ladder:
                strict_unclassified += 1
            if r.get("open_after", "na") != "na":
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
        print(
            f"   [ADR-1941] ranked by the OPEN SEGMENT. The attempts=-only"
            f" reading (attempts < {ladder}) would call"
            f" {strict_unclassified} rows UNCLASSIFIED;"
            f" {len(unclassified)} of them actually carry an open segment."
        )

        print("   -- classified give-up reasons (rankable), with ADR-1950 ms_left:")
        groups = collections.defaultdict(list)
        for r in classified:
            groups[bucket(r["giveup"])].append(r)
        for g, rows_ in sorted(groups.items(), key=lambda kv: -len(kv[1])):
            left = ms_left(rows_)
            if left:
                med = left[len(left) // 2]
                note = ("clock NOT binding" if med > BUDGET_MS * 0.5
                        else "clock-bound" if med < BUDGET_MS * 0.05 else "mixed")
                lt = (f"  ms_left min {left[0]} med {med} max {left[-1]}"
                      f"  [{note}]")
            else:
                lt = "  ms_left: none recorded"
            print(f"      {len(rows_):4d}  {g}")
            print(f"           {lt}")
            mags = magnitudes(rows_)
            if mags:
                cap = re.search(r"cap of (\d+)", rows_[0]["giveup"])
                capn = int(cap.group(1)) if cap else 0
                over = f" ({mags[0] / capn:.2f}x-{mags[-1] / capn:.2f}x)" if capn else ""
                print(
                    f"           measured N: min {mags[0]} median"
                    f" {mags[len(mags) // 2]} max {mags[-1]}{over}"
                )

        if unclassified:
            print("   -- UNCLASSIFIED: dispatch stopped early. NOT rankable by reason.")
            for k, c in collections.Counter(
                (r["attempts"], r["last"]) for r in unclassified
            ).most_common():
                print(f"      {c:4d}  attempts={k[0]} last={k[1]}")
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
