"""Read the outer-read-over-write sweep and print the sizing, the soundness
control, and the split that decides whether the gate is worth building.

Three things are printed and each answers a question the reach number alone
cannot:

1. **the reach** -- of a division's pinned winnable list, how many files does
   axeyum refute once the surrogate hands it outer read-over-write for free.
   Only `unsat` is counted; a surrogate `sat` is printed and counted nowhere.

2. **the soundness control** -- z3 on the ORIGINAL against z3 on the SURROGATE,
   per file.  Every accepted file is an opportunity for this to fire, not only
   the refutable ones, so the "no opinion" count is printed beside the zero
   (ADR-1957).

3. **the refutable denominator** -- outer read-over-write is a REFUTATION
   mechanism, so it cannot reach a satisfiable file at all.  The split of each
   winnable list into reference-`unsat` and reference-`sat` is therefore the
   ceiling on the gate, before any question of reach.  It is read from the
   board's own pinned TSVs, not re-measured here.

Usage:
    python3 summarize.py <sweepdir> [--board DIR] [--dist DIR]
"""

import collections
import os
import sys

BOARD_DEFAULT = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "..", "tier1-divisions-headtohead-20260913")
PREFIX = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"

# ADR-1957's census ceiling: files in the division behind the nested-array gate.
CEILING = {"AUFLIRA": 18510, "AUFNIRA": 955, "ALIA": 511, "ABV": 423}


def read_tsv(path):
    rows = []
    with open(path) as fh:
        head = fh.readline().rstrip("\n").split("\t")
        for line in fh:
            rows.append(dict(zip(head, line.rstrip("\n").split("\t"))))
    return rows


def reference_verdicts(board, div):
    """(z3, cvc5) per file from the board's pinned TSV, keyed by full path."""
    out = {}
    path = os.path.join(board, div + ".tsv")
    if not os.path.exists(path):
        return out
    for r in read_tsv(path):
        out[PREFIX + r["file"]] = (r.get("z3", ""), r.get("cvc5", ""))
    return out


def consensus(z, c):
    if z in ("sat", "unsat") and c in ("sat", "unsat") and z != c:
        return "CONFLICT"
    if z in ("sat", "unsat"):
        return z
    if c in ("sat", "unsat"):
        return c
    return "none"


def main(argv):
    sweep = argv[1]
    board = BOARD_DEFAULT
    dist = None
    i = 2
    while i < len(argv):
        if argv[i] == "--board":
            board = argv[i + 1]
            i += 2
        elif argv[i] == "--dist":
            dist = argv[i + 1]
            i += 2
        else:
            i += 1

    divisions = [d for d in ("AUFLIRA", "AUFNIRA", "ALIA", "ABV")
                 if os.path.exists(os.path.join(sweep, d + ".tsv"))]

    print("1. REACH -- what axeyum refutes when the surrogate hands it outer")
    print("   read-over-write for free.  Only `unsat` is counted.\n")
    print(f"| {'division':<9} | {'winnable':>8} | {'rewritten':>9} | {'refused':>7} "
          f"| {'ax unsat':>8} | {'ax sat*':>7} | {'reach':>6} | {'ceiling':>7} | {'projected':>9} |")
    print("|" + "|".join(["-" * n for n in (11, 10, 11, 9, 10, 9, 8, 9, 11)]) + "|")

    totals = collections.Counter()
    per_div = {}
    for div in divisions:
        rows = read_tsv(os.path.join(sweep, div + ".tsv"))
        ok = [r for r in rows if r["surrogate"] == "ok"]
        ref = [r for r in rows if r["surrogate"] == "REFUSED"]
        unsat = [r for r in ok if r["ax"] == "unsat"]
        sat = [r for r in ok if r["ax"] == "sat"]
        reach = f"{100.0 * len(unsat) / len(rows):.1f}%" if rows else "-"
        ceil = CEILING.get(div, 0)
        proj = int(round(ceil * len(unsat) / len(rows))) if rows else 0
        per_div[div] = (rows, ok, ref, unsat)
        totals["winnable"] += len(rows)
        totals["ok"] += len(ok)
        totals["refused"] += len(ref)
        totals["unsat"] += len(unsat)
        totals["projected"] += proj
        print(f"| {div:<9} | {len(rows):>8} | {len(ok):>9} | {len(ref):>7} "
              f"| {len(unsat):>8} | {len(sat):>7} | {reach:>6} | {ceil:>7} | {proj:>9} |")
    print(f"| {'**total**':<9} | {totals['winnable']:>8} | {totals['ok']:>9} "
          f"| {totals['refused']:>7} | {totals['unsat']:>8} | {'':>7} | {'':>6} "
          f"| {sum(CEILING[d] for d in divisions):>7} | {totals['projected']:>9} |")
    print("\n* a surrogate `sat` transfers nothing and is counted nowhere.\n")

    print("2. SOUNDNESS CONTROL -- z3 on the ORIGINAL vs z3 on the SURROGATE.")
    print("   Every ACCEPTED file is an opportunity, not only the refutable ones.\n")
    agree = differ = opportunity = noop = 0
    for div in divisions:
        _, ok, _, _ = per_div[div]
        for r in ok:
            zo, zs = r.get("z3_orig", ""), r.get("z3_surr", "")
            if zo in ("sat", "unsat") and zs in ("sat", "unsat"):
                opportunity += 1
                if zo == zs:
                    agree += 1
                else:
                    differ += 1
                    print(f"   CONTRADICTS: {r['file']}  original={zo} surrogate={zs}")
            else:
                noop += 1
    print(f"   z3 agrees {agree} / {opportunity}, no opinion {noop}, "
          f"CONTRADICTS {differ}")
    if opportunity == 0:
        print("   *** VACUOUS: the control had no opportunity to fire. ***")

    print("\n3. THE REFUTABLE DENOMINATOR -- outer read-over-write is a refutation")
    print("   mechanism, so a reference-`sat` file is outside its reach by")
    print("   construction, whatever the surrogate says.\n")
    print(f"| {'division':<9} | {'winnable':>8} | {'ref unsat':>9} | {'ref sat':>7} "
          f"| {'no ref':>6} | {'gate ceiling':>12} |")
    print("|" + "|".join(["-" * n for n in (11, 10, 11, 9, 8, 14)]) + "|")
    for div in divisions:
        rows, ok, _, unsat_rows = per_div[div]
        refs = reference_verdicts(board, div)
        c = collections.Counter()
        for r in rows:
            z, cv = refs.get(r["file"], ("", ""))
            c[consensus(z, cv)] += 1
        gate = int(round(CEILING.get(div, 0) * c["unsat"] / len(rows))) if rows else 0
        print(f"| {div:<9} | {len(rows):>8} | {c['unsat']:>9} | {c['sat']:>7} "
              f"| {c['none'] + c['CONFLICT']:>6} | {gate:>12} |")

    print("\n   `gate ceiling` = the division's ADR-1957 census ceiling scaled by the")
    print("   winnable list's reference-`unsat` rate.  It is the most the named gate")
    print("   could be worth even if every refutable file fell to it.\n")

    print("4. WHY THE REFUSED FILES WERE REFUSED -- and what the refusal names as")
    print("   the gate BEHIND this one.\n")
    for div in divisions:
        rows, _, ref, _ = per_div[div]
        refs = reference_verdicts(board, div)
        why = collections.Counter()
        for r in ref:
            base = os.path.basename(r["file"])
            found = None
            for n in range(1, len(rows) + 1):
                cand = os.path.join(sweep, "rewritten", div, f"{n}-{base}.why")
                if os.path.exists(cand):
                    found = open(cand).read().strip()
                    break
            key = "unparsed"
            if found:
                if "non-read position" in found or "bare value" in found:
                    key = "outer array EQUALITY (extensionality)"
                elif "outer array argument" in found:
                    key = "outer array passed to a function"
                elif "no outer array declaration" in found:
                    key = "no nested array at all"
                elif "OUTER array variable" in found:
                    key = "quantifies over an outer array"
                elif "nests" in found:
                    key = "nests deeper than 2"
                else:
                    key = found.split(":", 1)[-1].strip()[:50]
            z, cv = refs.get(r["file"], ("", ""))
            why[(key, consensus(z, cv))] += 1
        if not why:
            continue
        print(f"   {div}:")
        for (k, v), n in sorted(why.items(), key=lambda kv: -kv[1]):
            print(f"      {n:>3}  {k}  (reference: {v})")
        print()

    if dist:
        print("5. THE `--distribute` ARM -- the same sweep with `select` pushed")
        print("   through the array-sorted `ite` the expansion produces.\n")
        for div in divisions:
            p = os.path.join(dist, div + ".tsv")
            if not os.path.exists(p):
                continue
            drows = read_tsv(p)
            dok = [r for r in drows if r["surrogate"] == "ok"]
            dun = [r for r in dok if r["ax"] == "unsat"]
            _, ok, _, unsat_rows = per_div[div]
            print(f"   {div}: plain {len(unsat_rows)} / {len(ok)}   "
                  f"--distribute {len(dun)} / {len(dok)}   "
                  f"delta {len(dun) - len(unsat_rows):+d}")
        print()

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
