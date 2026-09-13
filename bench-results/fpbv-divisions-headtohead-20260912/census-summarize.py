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
    # Normalise the MEASURED quantity out of the reason so rows aggregate.
    # `has 1207 semantic atoms, exceeding the cap of 1024` and `has 1689 …` are
    # ONE blocker, and a ranking that prints them as two rows of 1 hides that
    # 53 of 87 files hit the same constant.  The magnitudes are not discarded --
    # they are reported as a range beside the count, because how far over a cap
    # a population runs is what decides whether raising it is worth doing.
    detail = re.sub(r"\b\d+\b", "N", detail)
    return f"{kind}: {detail[:110]}"


def magnitudes(rows_):
    """The measured quantities behind a normalised reason, for the range line."""
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

        # ADR-1941: the OPEN SEGMENT is the discriminator, not `attempts=` alone.
        # A row with no `route-open` line ran to the end of ITS OWN ladder --
        # ladder length is query-dependent, so `attempts=` below the division
        # maximum does not by itself mean the dispatch stopped.  A row WITH an
        # open segment had its budget vanish into code no route attempt covers,
        # and that is the row ADR-1936 exists to refuse to rank.
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

        # A TERMINAL INTERNAL ERROR is never RANKED as a capability blocker,
        # whatever ADR-1936 and ADR-1941 say about its dispatch.  It names a
        # defect in the code that raised it, not a fragment we cannot decide,
        # and ranking it beside real capability gaps would put a bug in a
        # build-this list.  It gets its own section below, WITH a repro path.
        # (Before ADR-1941 this exclusion happened by accident, because such a
        # row's low `attempts=` made it UNCLASSIFIED.  Now it is explicit --
        # which is the honest version, since the accident was never the reason.)
        errors = [r for r in classified if r["giveup"].startswith("give-up kind=Error")]
        classified = [
            r for r in classified if not r["giveup"].startswith("give-up kind=Error")
        ]

        print(
            f"   CLASSIFIED {len(classified)}   UNCLASSIFIED {len(unclassified)}"
            f"   no-route {len(noroute)}   decided-on-recheck {len(decided)}"
            f"   internal-error {len(errors)}"
        )
        # ADR-1941 step 6: publish BOTH readings whenever they differ, and say
        # which one is ranked.  The attempts=-only reading is evidence, not an
        # error to hide.
        print(
            f"   [ADR-1941] ranked by the OPEN SEGMENT. The attempts=-only"
            f" reading (attempts < {ladder}) would call"
            f" {strict_unclassified} rows UNCLASSIFIED;"
            f" {len(unclassified)} of them actually carry an open segment."
        )

        print("   -- classified give-up reasons (rankable):")
        groups = collections.defaultdict(list)
        for r in classified:
            groups[bucket(r["giveup"])].append(r)
        for g, rows_ in sorted(groups.items(), key=lambda kv: -len(kv[1])):
            print(f"      {len(rows_):4d}  {g}")
            mags = magnitudes(rows_)
            if mags:
                cap = re.search(r"cap of (\d+)", rows_[0]["giveup"])
                capn = int(cap.group(1)) if cap else 0
                over = f" ({mags[0] / capn:.2f}x-{mags[-1] / capn:.2f}x)" if capn else ""
                print(
                    f"            measured N: min {mags[0]} median"
                    f" {mags[len(mags) // 2]} max {mags[-1]}{over}"
                )

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

        # A TERMINAL INTERNAL ERROR is reported whatever `attempts=` says.
        # ADR-1936's UNCLASSIFIED rule exists because a give-up reason from a
        # dispatch that stopped early describes the DISPATCHER.  An internal
        # error message does not: it names a defect in the code that raised it,
        # and it is a finding at any attempts count.  It is still excluded from
        # the rankable bucket -- it is listed, not ranked.
        err = [r for r in rs if r["giveup"].startswith("give-up kind=Error")]
        if err:
            print(f"   -- TERMINAL INTERNAL ERROR: {len(err)} (reported at any attempts=)")
            for k, c in collections.Counter(
                r["giveup"][len("give-up kind=Error detail="):][:150] for r in err
            ).most_common():
                print(f"      {c:4d}  {k}")
                for r in err:
                    if r["giveup"][len("give-up kind=Error detail="):][:150] == k:
                        print(f"            repro: {r['file']}")
                        break
        print()
    return 0 if any_seen else 1


if __name__ == "__main__":
    sys.exit(main())
