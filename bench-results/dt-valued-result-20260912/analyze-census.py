#!/usr/bin/env python3
"""Reproduce every number in the ADR-1946 sizing note from the committed rows.

    python3 bench-results/dt-valued-result-20260912/analyze-census.py

A record (`C` row) is one entry into the datatype route, carrying the
classification of EVERY datatype-sorted uninterpreted-function argument and
EVERY collected function's result sort under the WIDENED collection rule -- not
the first refusal, which is what makes this a reachability count rather than a
blocker count.

TWO PREDICATES, AND BOTH ARE PRINTED. The ADR-1942 sizing note's §7 correction
is the reason: the datatype route is entered MANY times per file (MBQI and
e-matching hand it a fresh residual after each round), and the file decides when
ONE of those entries is handled. So `all(entries eligible)` is neither an upper
nor a lower bound, and the honest sizing is the bracket
[all-entries, any-entry].
"""

import collections
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CENSUS = os.path.join(HERE, "census")
DIVS = ["AUFDTLIRA", "UFDTLIRA", "UFDT"]
MAX_ACK_PAIRS = 20_000

# Every spelling of the shape refusal, across the three arms that have worded it.
SHAPE_REFUSALS = (
    "not a free variable",
    "neither a free variable nor a constructor",
    "nor another uninterpreted",
)


def load(div):
    out = {}
    with open(os.path.join(CENSUS, f"{div}.tsv")) as fh:
        for line in fh:
            if line.startswith("#"):
                continue
            p = line.rstrip("\n").split("\t")
            if p[0] == "F":
                out.setdefault(p[1], {"recs": []})
                out[p[1]]["verdict"] = p[2]
                out[p[1]]["giveup"] = p[3]
            elif p[0] == "C":
                rec = {}
                for tok in p[3].split()[1:]:
                    k, _, v = tok.partition("=")
                    rec[k] = v
                out.setdefault(p[1], {"recs": []})["recs"].append(rec)
    return out


def bucket(row):
    if row["verdict"] in ("sat", "unsat"):
        return "decided"
    g = row["giveup"]
    if any(t in g for t in SHAPE_REFUSALS):
        return "non-variable/non-ctor dt argument"
    if "expansion is not exact" in g:
        return "inexact expansion"
    if "RESULT sort mentions a datatype" in g:
        return "dt-valued UF result"
    if "non-variable datatype term" in g:
        return "is/select non-variable"
    if g in ("WRAPPER-KILLED", "RC134-ABORT", "SIGKILL", "none"):
        return g
    import re

    m = re.search(r"detail=(.*)", g)
    return "other: " + (m.group(1) if m else g)[:52]


def n(r, k):
    return int(r.get(k, 0))


def entry_c(r):
    """Is THIS entry into the datatype route eligible under ADR-1946?"""
    return (
        n(r, "sym_inexact") == 0
        and n(r, "ctor_inexact") == 0
        and n(r, "apply_inexact") == 0
        and n(r, "other") == 0
        and n(r, "dtres_inexact") == 0
        and n(r, "dtres_nondt") == 0
        and n(r, "wide_pairs") <= MAX_ACK_PAIRS
    )


def entry_a(r):
    """Is THIS entry eligible on the arm as it stands (ADR-1942)?"""
    return (
        n(r, "sym_inexact") == 0
        and n(r, "ctor_inexact") == 0
        and n(r, "apply_exact") == 0
        and n(r, "apply_inexact") == 0
        and n(r, "other") == 0
        and n(r, "dtres_funcs") == 0
        and n(r, "dtres_nondt") == 0
        and n(r, "narrow_pairs") <= MAX_ACK_PAIRS
    )


rows = []
for div in DIVS:
    for path, row in load(div).items():
        recs = row["recs"]
        rows.append(
            dict(
                div=div,
                path=path,
                bucket=bucket(row),
                verdict=row["verdict"],
                # the committed ELIGIBLE_* flags, recomputed here so the note's
                # numbers do not depend on the instrumentation's own arithmetic
                all_a=bool(recs) and all(entry_a(r) for r in recs),
                any_a=any(entry_a(r) for r in recs),
                all_c=bool(recs) and all(entry_c(r) for r in recs),
                any_c=any(entry_c(r) for r in recs),
                # what the widening ADDS, and what it might cost
                new_sites=any(n(r, "wide_sites") > n(r, "narrow_sites") for r in recs),
                dtres=any(n(r, "dtres_funcs") > 0 for r in recs),
                dtres_inexact=any(n(r, "dtres_inexact") > 0 for r in recs),
                dtres_nondt=any(n(r, "dtres_nondt") > 0 for r in recs),
                apply_arg=any(n(r, "apply_exact") + n(r, "apply_inexact") > 0 for r in recs),
                apply_exact=any(n(r, "apply_exact") > 0 for r in recs),
                sym_inexact=any(n(r, "sym_inexact") > 0 for r in recs),
                ctor_inexact=any(n(r, "ctor_inexact") > 0 for r in recs),
                other=any(n(r, "other") > 0 for r in recs),
                # THE COST OF THE WIDENING: a file whose narrow pair count is
                # within bound but whose WIDE count is not loses the whole
                # Ackermann pre-pass, so it can go from decided to declined.
                pairs_blowup=any(
                    n(r, "narrow_pairs") <= MAX_ACK_PAIRS < n(r, "wide_pairs") for r in recs
                ),
                max_wide_pairs=max([n(r, "wide_pairs") for r in recs], default=0),
                has_recs=bool(recs),
            )
        )

assert len(rows) == 600, f"expected 600 rows, got {len(rows)}"

DECIDED = lambda r: r["bucket"] == "decided"
UNDEC = lambda r: not DECIDED(r)


def line(label, pred, subset=None):
    per = collections.Counter()
    for r in rows:
        if subset and not subset(r):
            continue
        if pred(r):
            per[r["div"]] += 1
    print(f"  {label:58} " + " ".join(f"{per[d]:>6}" for d in DIVS) + f" {sum(per.values()):>7}")


print("                                                             " + " ".join(f"{d:>6}" for d in DIVS) + "   total")
print("\n=== 1. Where the 600 stand on the ADR-1942 arm (this lane's BASE) ===\n")
counts = collections.Counter(r["bucket"] for r in rows)
for b, _ in counts.most_common(9):
    line(b, lambda r, b=b: r["bucket"] == b)

print("\n=== 2. What this lane's widening reaches, as a BRACKET (ADR-1942 note §7) ===\n")
print("  -- over the UNDECIDED files only, which is the population a gain comes from --\n")
line("ADR-1946 eligible, EVERY route entry", lambda r: r["all_c"], UNDEC)
line("ADR-1946 eligible, ANY route entry", lambda r: r["any_c"], UNDEC)
print()
line("the arm as it stands, EVERY route entry", lambda r: r["all_a"], UNDEC)
line("the arm as it stands, ANY route entry", lambda r: r["any_a"], UNDEC)
print()
# The two "newly" lines are DIFFERENT populations, not nested: a file can be
# ANY-eligible on both arms (so not newly-ANY) while only the new arm makes
# EVERY entry eligible.
line("newly eligible under the ANY predicate", lambda r: r["any_c"] and not r["any_a"], UNDEC)
line("newly eligible under the EVERY predicate", lambda r: r["all_c"] and not r["all_a"], UNDEC)
print()
print("  -- the same two predicates over all 600, comparable to the ADR-1942 note's")
print("     slice-B figures (EVERY 176, ANY 285, measured on the PREVIOUS arm) --\n")
line("ADR-1946 eligible, EVERY route entry, all 600", lambda r: r["all_c"])
line("ADR-1946 eligible, ANY route entry, all 600", lambda r: r["any_c"])

print("\n=== 3. Which half of the widening does the work ===\n")
line("undecided files that collect a NEW site under the wide rule",
     lambda r: r["new_sites"], UNDEC)
line("undecided files with a datatype-VALUED UF result", lambda r: r["dtres"], UNDEC)
line("undecided files with an Op::Apply datatype ARGUMENT", lambda r: r["apply_arg"], UNDEC)
line("  ... over an EXACT datatype (the admissible ones)", lambda r: r["apply_exact"], UNDEC)

print("\n=== 4. What is still refused, among the newly ineligible ===\n")
line("blocked by a VARIABLE over an inexact datatype", lambda r: r["sym_inexact"], UNDEC)
line("blocked by a CONSTRUCTOR over an inexact datatype", lambda r: r["ctor_inexact"], UNDEC)
line("blocked by an Op::Apply over an INEXACT datatype", lambda r: r["any_c"] is False and r["apply_arg"], UNDEC)
line("blocked by an INEXACT datatype-valued RESULT", lambda r: r["dtres_inexact"], UNDEC)
line("blocked by an ARRAY-over-datatype RESULT", lambda r: r["dtres_nondt"], UNDEC)
line("blocked by some other term shape", lambda r: r["other"], UNDEC)

print("\n=== 5. THE COST: files the widening could take AWAY ===\n")
line("DECIDED files pushed OVER the pair bound by the widening",
     lambda r: r["pairs_blowup"], DECIDED)
line("any file pushed OVER the pair bound by the widening", lambda r: r["pairs_blowup"])
line("any file whose WIDE pair count is over the bound at all",
     lambda r: r["max_wide_pairs"] > MAX_ACK_PAIRS)
line("DECIDED files that collect a NEW site under the wide rule",
     lambda r: r["new_sites"], DECIDED)
line("  ... of those, NOT eligible at every entry (the pass will refuse)",
     lambda r: r["new_sites"] and not r["all_c"], DECIDED)
worst = sorted((r for r in rows if r["new_sites"]), key=lambda r: -r["max_wide_pairs"])[:5]
print("\n  largest wide pair counts among files gaining sites:")
for r in worst:
    print(f"    {r['max_wide_pairs']:>8}  {r['div']:10} {r['bucket'][:30]:32} {r['path'][:70]}")

print("\n=== 6. The newly-eligible population, named (ANY-entry predicate) ===\n")
newly = [r for r in rows if UNDEC(r) and r["any_c"] and not r["any_a"]]
for r in sorted(newly, key=lambda r: (r["div"], r["path"])):
    print(f"  {r['div']:10} {r['bucket'][:34]:36} {r['path']}")
print(f"\n  ({len(newly)} files)")
