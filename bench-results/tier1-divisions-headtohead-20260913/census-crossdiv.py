"""Roll the seven per-division censuses up into ONE cross-division table.

ADR-1950 governs the shape: every family carries a `kind` naming WHICH budget
or shape stopped it, and an `ms_left` distribution that can falsify that kind.

  CLOCK  the wall-clock budget ran out          (raising it costs wall time)
  ROUND  a ROUND COUNT ran out, with clock left (a different lever entirely)
  SHAPE  a route declined a fragment            (neither budget helps)
  PARSE  the FRONT DOOR refused the file        (it never reached a route)

PARSE is a kind this lane adds and it is the lane's headline question.  A parse
refusal arrives as `give-up kind=Error`, which board-six's census excluded from
ranking as an "internal error".  That exclusion is right for a panic or an
internal invariant failure; it is wrong for a front-door refusal of legal
SMT-LIB, which is a capability statement about the IR and is exactly what the
NESTED-ARRAY-IR lane is sizing.  So parse refusals are ranked here, under their
own kind, and the `OTHER` bucket is printed in full so a catch-all cannot
quietly absorb a family and leave a stable-looking total.

ADR-1941 governs which rows may be counted at all: UNCLASSIFIED rows (those
with a `route-open` segment) are excluded from every number below and reported
separately, because their give-up reason describes the dispatcher.
"""

import collections
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
DIVS = ["AUFLIRA", "UFNIA", "ABV", "ALIA", "AUFNIRA", "AUFBV", "FP"]
BUDGET_MS = 24_000

# (label, kind, matcher) -- order matters, first match wins.
FAMILIES = [
    ("nested array element sort refused (PARSE)", "PARSE",
     lambda g: "nested array element sort is unsupported" in g),
    ("other front-door parse refusal", "PARSE",
     lambda g: "parse error" in g),
    # A `kind=Error` that is NOT a parse refusal names a defect in the code
    # that raised it, not a fragment we cannot decide.  It gets its own kind so
    # it can never be read as a capability gap to go and build.
    ("terminal internal error (NOT a capability gap)", "INTERNAL",
     lambda g: g.startswith("give-up kind=Error")),
    ("e-matching ROUND budget", "ROUND",
     lambda g: "e-matching instantiation did not refute within the round budget" in g),
    ("e-matching CLOCK budget", "CLOCK",
     lambda g: "quantified solve time budget exhausted after e-matching" in g),
    ("e-matching instantiation CLOCK", "CLOCK",
     lambda g: "e-matching: instantiation time budget exhausted" in g),
    ("e-matching has no universal", "SHAPE",
     lambda g: "e-matching: no universal is asserted" in g),
    ("mbqi declined an unsupported fragment", "SHAPE",
     lambda g: "mbqi declined an unsupported fragment" in g),
    ("MBQI round budget", "ROUND",
     lambda g: "MBQI did not converge within" in g),
    ("finite domain too big to expand", "SHAPE",
     lambda g: "exceeds the eager expansion budget" in g),
    ("instantiation sat, universal unrefuted", "SHAPE",
     lambda g: "instantiation is satisfiable; the universal may still be violated" in g),
    ("array lazy-ROW / extensionality", "ARRAY",
     lambda g: "lazy-ROW" in g or "lazy-extensionality" in g),
    ("semantic atom / DAG node cap", "SHAPE",
     lambda g: "exceeding the cap of" in g),
    ("unsupported by backend", "SHAPE",
     lambda g: "unsupported by backend" in g),
    ("quantified CLOCK, other stage", "CLOCK",
     lambda g: "quantified solve time budget exhausted after" in g),
    ("no give-up line recorded", "NONE",
     lambda g: g in ("none", "")),
]


def norm(g):
    g = re.sub(r"\bList\(\[.*", "<SORT>", g)
    return re.sub(r"\b\d+\b", "N", g)


def classify(g):
    for label, kind, m in FAMILIES:
        if m(g):
            return label, kind
    return f"OTHER: {norm(g)[:80]}", "OTHER"


def main():
    per_div = {}
    rows_by_family = collections.defaultdict(list)
    unclass = collections.Counter()
    decided = collections.Counter()
    total_rows = 0
    missing = []
    for div in DIVS:
        p = HERE / "census" / f"{div}.tsv"
        if not p.exists():
            missing.append(div)
            per_div[div] = collections.Counter()
            continue
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
                decided[div] += 1
                continue
            label, kind = classify(r["giveup"])
            c[label] += 1
            rows_by_family[(label, kind)].append((div, r))
        per_div[div] = c

    if missing:
        print(f"!! census DID NOT RUN for: {', '.join(missing)} "
              f"-- their columns below are structurally zero, not a finding\n")

    print(f"census rows total: {total_rows}   UNCLASSIFIED (ADR-1941): "
          f"{sum(unclass.values())}  {dict(unclass)}   "
          f"decided-on-recheck: {sum(decided.values())}  {dict(decided)}\n")

    hdr = (f"{'family':44s} {'kind':6s} "
           + " ".join(f"{d[:8]:>8s}" for d in DIVS) + "   tot")
    print(hdr)
    print("-" * len(hdr))
    order = sorted(rows_by_family, key=lambda k: -len(rows_by_family[k]))
    for label, kind in order:
        cells = " ".join(f"{per_div[d][label]:8d}" for d in DIVS)
        print(f"{label:44s} {kind:6s} {cells} {len(rows_by_family[(label, kind)]):5d}")

    by_kind = collections.Counter()
    for (label, kind), rs in rows_by_family.items():
        by_kind[kind] += len(rs)
    print(f"\nby kind: {dict(by_kind.most_common())}")

    # ADR-1950: the remaining-budget distribution is what falsifies a `kind`.
    print("\nremaining budget at give-up (ms_left = 24000 - total_ms), per family:")
    print(f"{'family':44s} {'kind':6s} {'n':>4s} {'min':>7s} {'med':>7s} "
          f"{'max':>7s}   note")
    for label, kind in order:
        left = []
        for _div, r in rows_by_family[(label, kind)]:
            try:
                left.append(BUDGET_MS - int(r["total_ms"]))
            except (ValueError, KeyError):
                pass
        if not left:
            print(f"{label:44s} {kind:6s} {'-':>4s} {'-':>7s} {'-':>7s} "
                  f"{'-':>7s}   no total_ms recorded")
            continue
        left.sort()
        med = left[len(left) // 2]
        note = ("FAST DECLINE -- clock was NOT the binding constraint"
                if med > BUDGET_MS * 0.5 else
                "clock-bound" if med < BUDGET_MS * 0.05 else "mixed")
        print(f"{label:44s} {kind:6s} {len(left):4d} {left[0]:7d} {med:7d} "
              f"{left[-1]:7d}   {note}")

    # The lane's headline question, answered with its own denominator.
    print("\n== the nested-array parse refusal, per division ==")
    nested = [
        (d, r) for (label, _k), rs in rows_by_family.items()
        if label.startswith("nested array") for d, r in rs
    ]
    bydiv = collections.Counter(d for d, _ in nested)
    print(f"{'division':10s} {'winnable':>9s} {'nested-array':>13s} {'share':>7s}")
    for div in DIVS:
        wf = HERE / "winnable" / f"{div}.txt"
        w = len([x for x in wf.read_text().split("\n") if x]) if wf.exists() else 0
        s = f"{bydiv[div] / w:.0%}" if w else "n/a"
        print(f"{div:10s} {w:9d} {bydiv[div]:13d} {s:>7s}")
    tot_w = sum(
        len([x for x in (HERE / "winnable" / f"{d}.txt").read_text().split("\n") if x])
        for d in DIVS if (HERE / "winnable" / f"{d}.txt").exists()
    )
    print(f"{'TOTAL':10s} {tot_w:9d} {len(nested):13d} "
          f"{len(nested) / tot_w:>7.0%}" if tot_w else "")

    # Print the OTHER bucket in FULL.  A catch-all that absorbs a family leaves
    # a total that looks stable and is wrong; this makes that visible.
    print("\n== OTHER bucket, in full (a catch-all must not hide a family) ==")
    other = [(lab, rs) for (lab, k), rs in rows_by_family.items() if k == "OTHER"]
    if not other:
        print("   (empty)")
    for lab, rs in sorted(other, key=lambda kv: -len(kv[1])):
        print(f"   {len(rs):4d}  {lab}")
        print(f"         repro: {rs[0][1]['file']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
