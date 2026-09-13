"""Roll the six per-division censuses up into ONE cross-division table.

The brief for this lane predicted that the dominant non-array blocker across
AUFLIA / UFLIA / LRA / UFNIA would be `quantified solve time budget exhausted
after e-matching`, and that if it held at n=200 it is one finding rather than
five.  This script is the test, and it splits the e-matching family by the thing
that decides what to do about it:

  CLOCK  the wall-clock budget ran out          (raising it costs wall time)
  ROUND  a ROUND COUNT ran out, with clock left (a different lever entirely)
  SHAPE  e-matching had nothing to instantiate   (neither budget helps)

A ranking that merges those three says "e-matching" and tells you nothing.  The
`ms_left` column is what separates them: median remaining budget at the moment
the row gave up.  It is derived, not asserted -- a ROUND-capped row that
actually burns the clock would show up here as ms_left ~ 0 and be reclassified
by the data.

ADR-1941 governs which rows may be counted at all: UNCLASSIFIED rows (those
with a `route-open` segment) are excluded from every number below and reported
separately, because their give-up reason describes the dispatcher.
"""

import collections
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
DIVS = ["NRA", "QF_AUFLIA", "BV", "AUFLIA", "UFLIA", "LRA"]
BUDGET_MS = 24_000

# (label, kind, matcher) -- order matters, first match wins.
FAMILIES = [
    ("e-matching ROUND budget", "ROUND",
     lambda g: "e-matching instantiation did not refute within the round budget" in g),
    ("e-matching CLOCK budget", "CLOCK",
     lambda g: "quantified solve time budget exhausted after e-matching" in g),
    ("e-matching instantiation CLOCK", "CLOCK",
     lambda g: "e-matching: instantiation time budget exhausted" in g),
    ("e-matching has no universal", "SHAPE",
     lambda g: "e-matching: no universal is asserted" in g),
    ("mbqi -> BV backend, uninterpreted sort", "SHAPE",
     lambda g: "mbqi declined an unsupported fragment" in g),
    ("MBQI round budget", "ROUND",
     lambda g: "MBQI did not converge within" in g),
    ("finite BV domain too big to expand", "SHAPE",
     lambda g: "exceeds the eager expansion budget" in g),
    ("instantiation sat, universal unrefuted", "SHAPE",
     lambda g: "instantiation is satisfiable; the universal may still be violated" in g),
    ("array lazy-ROW / extensionality", "ARRAY",
     lambda g: "lazy-ROW" in g or "lazy-extensionality" in g),
    ("quantified CLOCK, other stage", "CLOCK",
     lambda g: "quantified solve time budget exhausted after" in g),
]


def classify(g):
    for label, kind, m in FAMILIES:
        if m(g):
            return label, kind
    return f"OTHER: {g[:70]}", "OTHER"


def main():
    per_div = {}
    rows_by_family = collections.defaultdict(list)
    unclass = collections.Counter()
    total_rows = 0
    for div in DIVS:
        p = HERE / "census" / f"{div}.tsv"
        if not p.exists():
            print(f"{div}: census DID NOT RUN")
            return 1
        lines = p.read_text().rstrip("\n").split("\n")
        head = lines[0].split("\t")
        rs = [dict(zip(head, ln.split("\t"))) for ln in lines[1:]]
        total_rows += len(rs)
        c = collections.Counter()
        for r in rs:
            # ADR-1941: an open segment means the dispatch did not finish.
            if r.get("open_after", "na") != "na":
                unclass[div] += 1
                continue
            if r["verdict"] in ("sat", "unsat"):
                continue
            label, kind = classify(r["giveup"])
            c[label] += 1
            rows_by_family[(label, kind)].append((div, r))
        per_div[div] = c

    print(f"census rows total: {total_rows}   UNCLASSIFIED (ADR-1941): "
          f"{sum(unclass.values())}  {dict(unclass)}\n")

    hdr = f"{'family':42s} {'kind':6s} " + " ".join(f"{d[:9]:>9s}" for d in DIVS) + "   tot"
    print(hdr)
    print("-" * len(hdr))
    order = sorted(rows_by_family, key=lambda k: -len(rows_by_family[k]))
    for label, kind in order:
        cells = " ".join(f"{per_div[d][label]:9d}" for d in DIVS)
        print(f"{label:42s} {kind:6s} {cells} {len(rows_by_family[(label, kind)]):5d}")

    by_kind = collections.Counter()
    for (label, kind), rs in rows_by_family.items():
        by_kind[kind] += len(rs)
    print(f"\nby kind: {dict(by_kind.most_common())}")

    print("\nremaining budget at give-up (ms_left = 24000 - total_ms), per family:")
    print(f"{'family':42s} {'kind':6s} {'n':>4s} {'min':>7s} {'med':>7s} "
          f"{'max':>7s}   note")
    for label, kind in order:
        left = []
        for _div, r in rows_by_family[(label, kind)]:
            try:
                left.append(BUDGET_MS - int(r["total_ms"]))
            except (ValueError, KeyError):
                pass
        if not left:
            continue
        left.sort()
        med = left[len(left) // 2]
        note = ("FAST DECLINE -- clock was NOT the binding constraint"
                if med > BUDGET_MS * 0.5 else
                "clock-bound" if med < BUDGET_MS * 0.05 else "mixed")
        print(f"{label:42s} {kind:6s} {len(left):4d} {left[0]:7d} {med:7d} "
              f"{left[-1]:7d}   {note}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
