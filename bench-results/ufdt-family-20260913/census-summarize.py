"""The UFNIA / UFLIA blocker census, over the WHOLE winnable set of each.

Run from this directory:  python3 census-summarize.py

Four ADRs govern what may be said:

ADR-1936  a row whose dispatch did not reach the end of the ladder is
          UNCLASSIFIED and is NEVER reported by its give-up reason.
ADR-1941  `attempts=` alone cannot make that call -- the discriminator is the
          `route-open` SEGMENT.  Both readings are printed on every division.
ADR-1950  a "budget exhausted" family carries a `kind` naming WHICH budget and
          the min/median/max of budget REMAINING, which can falsify the kind.
ADR-1956  the e-matching loop's three exits (fixpoint / growth-headroom / round
          ceiling) are DISTINCT strings.  A census that folds them reads three
          causes as one; `census_kind()` in the solver assigns SHAPE / CLOCK /
          ROUND respectively and this table uses the same assignment.
"""

import collections
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
DIVS = ["UFDTNIRA", "UFDTLIRA", "UFDT", "AUFDTLIRA"]
BUDGET_MS = 24_000

# (label, kind, matcher) -- order matters, first match wins.
FAMILIES = [
    # --- ADR-1956: the three e-matching loop exits, kept apart ---------------
    ("e-matching FIXPOINT (no instance left to admit)", "SHAPE",
     lambda g: "reached fixpoint without refuting" in g),
    ("e-matching GROWTH-HEADROOM (a clock exit)", "CLOCK",
     lambda g: "could not fit another round with growth headroom" in g),
    ("e-matching ROUND CEILING (the round budget)", "ROUND",
     lambda g: "did not refute within the round budget" in g),
    # --- front door ----------------------------------------------------------
    ("front-door parse refusal", "PARSE",
     lambda g: "parse error" in g),
    ("terminal internal error (NOT a capability gap)", "INTERNAL",
     lambda g: g.startswith("give-up kind=Error")),
    # --- the quantified ladder ----------------------------------------------
    ("ladder CLOCK exhausted after e-matching", "CLOCK",
     lambda g: "quantified solve time budget exhausted after e-matching" in g),
    ("e-matching instantiation CLOCK", "CLOCK",
     lambda g: "e-matching: instantiation time budget exhausted" in g),
    ("e-matching GROUND-TERM budget", "SHAPE",
     lambda g: "e-matching: ground-term count budget exhausted" in g),
    ("e-matching has no universal", "SHAPE",
     lambda g: "e-matching: no universal is asserted" in g),
    # `mbqi declined an unsupported fragment: ...` is a PREFIX shared by every
    # MBQI refusal, and on these divisions it covers at least four unrelated
    # causes -- three of them the named datatype-exactness preconditions of
    # ADR-1920 / ADR-1935 / ADR-1946, and one an ordinary BV sort refusal. A
    # single bucket for the prefix is ADR-1956's defect verbatim: three causes
    # read as one, and the biggest of them invisible. They are split here by
    # the text AFTER the colon.
    ("mbqi: datatype ARGUMENT congruence not exact (ADR-1935)", "SHAPE",
     lambda g: "congruence over a datatype argument whose expansion is not exact" in g),
    ("mbqi: UF applied to a non-atomic datatype term (ADR-1920/1942)", "SHAPE",
     lambda g: "an uninterpreted function applied to a datatype term that is neither" in g),
    ("mbqi: datatype RESULT expansion not exact (ADR-1946)", "SHAPE",
     lambda g: "whose RESULT datatype's expansion is not exact" in g),
    ("mbqi: uninterpreted sort the BV backend cannot blast", "SHAPE",
     lambda g: "mbqi declined an unsupported fragment" in g
     and "that the pure-Rust BV backend cannot bit-blast" in g),
    ("mbqi declined an unsupported fragment, OTHER cause", "SHAPE",
     lambda g: "mbqi declined an unsupported fragment" in g),
    ("MBQI round budget", "ROUND",
     lambda g: "MBQI did not converge within" in g),
    ("finite domain too big to expand", "SHAPE",
     lambda g: "exceeds the eager expansion budget" in g),
    ("instantiation sat, universal unrefuted", "SHAPE",
     lambda g: "instantiation is satisfiable; the universal may still be violated" in g),
    # ADR-1950's rule applied to `quantified_timeout`'s OWN stage name. Every
    # one of these reads `quantified solve time budget exhausted after <stage>`
    # and a single bucket would report FOUR different rungs as one finding --
    # the same collapse ADR-1956 found inside the e-matching loop, one level
    # up. `q:valid-universal-qf` is the one that matters on UFDTNIRA and it is
    # named here so it can never be read as "the quantified ladder is slow".
    ("valid-universal elimination CLOCK", "CLOCK",
     lambda g: "budget exhausted after valid-universal elimination" in g),
    ("vacuous-universal elimination CLOCK", "CLOCK",
     lambda g: "budget exhausted after vacuous-universal elimination" in g),
    ("existential skolemization CLOCK", "CLOCK",
     lambda g: "budget exhausted after existential skolemization" in g),
    ("quantifier normalization CLOCK", "CLOCK",
     lambda g: "budget exhausted after quantifier normalization" in g),
    ("quantified CLOCK, unnamed stage", "CLOCK",
     lambda g: "quantified solve time budget exhausted after" in g),
    # --- ingest / capacity ---------------------------------------------------
    ("ingest resource limit (deterministic cap)", "SHAPE",
     lambda g: "ingest resource limit" in g),
    ("lazy Ackermann congruence-term cap", "SHAPE",
     lambda g: "congruence terms, exceeding" in g),
    ("bounded integer width", "SHAPE",
     lambda g: "no model within the bounded integer width" in g),
    ("semantic atom / DAG node cap", "SHAPE",
     lambda g: "exceeding the cap of" in g),
    ("unsupported by backend", "SHAPE",
     lambda g: "unsupported by backend" in g),
    ("watchdog fired before the worker returned", "WATCHDOG",
     lambda g: "watchdog fired" in g),
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


def read(div):
    p = HERE / "census" / f"{div}.winnable.tsv"
    if not p.exists():
        return None
    lines = p.read_text().rstrip("\n").split("\n")
    head = lines[0].split("\t")
    return [dict(zip(head, ln.split("\t"))) for ln in lines[1:]]


def main():
    rows_by_family = collections.defaultdict(list)
    per_div = collections.defaultdict(collections.Counter)
    unclass, decided, noroute = collections.Counter(), collections.Counter(), collections.Counter()
    strict_unclass = collections.Counter()
    missing, seen = [], 0

    for div in DIVS:
        rs = read(div)
        if rs is None:
            missing.append(div)
            continue
        seen += 1
        numeric = [int(r["attempts"]) for r in rs if r["attempts"].isdigit()]
        ladder = max(numeric) if numeric else 0
        print(f"== {div}  census rows={len(rs)}  ladder(empirical max attempts)={ladder}")
        print(f"   attempts distribution: "
              f"{dict(sorted(collections.Counter(r['attempts'] for r in rs).items(), key=str))}")
        print(f"   wrapper-killed rc=124: {sum(r['rc'] == '124' for r in rs)}"
              f"   rc134 (8 GiB cap): {sum(r['rc'] == '134' for r in rs)}")
        for r in rs:
            a = r["attempts"]
            if not a.isdigit():
                noroute[div] += 1
                continue
            if int(a) < ladder:
                strict_unclass[div] += 1
            if r.get("open_after", "na") != "na":
                unclass[div] += 1
                continue
            if r["verdict"] in ("sat", "unsat"):
                decided[div] += 1
                continue
            label, kind = classify(r["giveup"])
            per_div[div][label] += 1
            rows_by_family[(label, kind)].append((div, r))
        print(f"   [ADR-1941] ranked by the OPEN SEGMENT. The attempts=-only reading"
              f" (attempts < {ladder}) would call {strict_unclass[div]} rows UNCLASSIFIED;"
              f" {unclass[div]} actually carry an open segment.")
        print(f"   UNCLASSIFIED {unclass[div]}   no-route {noroute[div]}"
              f"   decided-on-this-run {decided[div]}\n")

    if missing:
        print(f"!! census DID NOT RUN for: {', '.join(missing)} -- their columns are"
              f" structurally zero, not a finding\n")
    if not seen:
        return 1

    order = sorted(rows_by_family, key=lambda k: -len(rows_by_family[k]))
    hdr = f"{'family':48s} {'kind':8s} " + " ".join(f"{d:>7s}" for d in DIVS) + "   tot"
    print(hdr)
    print("-" * len(hdr))
    for label, kind in order:
        cells = " ".join(f"{per_div[d][label]:7d}" for d in DIVS)
        print(f"{label:48s} {kind:8s} {cells} {len(rows_by_family[(label, kind)]):5d}")

    by_kind = collections.Counter()
    for (label, kind), rs in rows_by_family.items():
        by_kind[kind] += len(rs)
    print(f"\nby kind: {dict(by_kind.most_common())}")
    print(f"UNCLASSIFIED (ADR-1941, excluded from every count above): "
          f"{sum(unclass.values())}  {dict(unclass)}")
    print(f"no route trail at all: {sum(noroute.values())}  {dict(noroute)}")

    print("\nADR-1950 -- remaining budget at give-up (ms_left = 24000 - total_ms):")
    print(f"{'family':48s} {'kind':8s} {'n':>4s} {'min':>7s} {'med':>7s} {'max':>7s}   note")
    for label, kind in order:
        left = []
        for _d, r in rows_by_family[(label, kind)]:
            try:
                left.append(BUDGET_MS - int(r["total_ms"]))
            except (ValueError, KeyError):
                pass
        if not left:
            print(f"{label:48s} {kind:8s} {'-':>4s} {'-':>7s} {'-':>7s} {'-':>7s}"
                  f"   no total_ms recorded")
            continue
        left.sort()
        med = left[len(left) // 2]
        note = ("FAST DECLINE -- clock was NOT the binding constraint"
                if med > BUDGET_MS * 0.5 else
                "clock-bound" if med < BUDGET_MS * 0.05 else "MIXED -- two populations")
        print(f"{label:48s} {kind:8s} {len(left):4d} {left[0]:7d} {med:7d} {left[-1]:7d}   {note}")

    print("\nrows that gave up PAST the 24,000 ms deadline, by kind"
          " (the direct test of the labels):")
    for kind in ("CLOCK", "ROUND", "SHAPE", "PARSE", "WATCHDOG", "OTHER", "INTERNAL", "NONE"):
        rs = [r for (lab, k), v in rows_by_family.items() if k == kind for _d, r in v]
        if not rs:
            continue
        past = sum(1 for r in rs
                   if r["total_ms"].lstrip("-").isdigit() and int(r["total_ms"]) > BUDGET_MS)
        print(f"   {kind:9s} {past:4d} of {len(rs):4d}")

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
