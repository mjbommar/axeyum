"""The board row for this lane's arm, and the winnable set the census covers.

Our verdicts come from THIS lane's run (`census/<div>.tsv`); the z3 / cvc5 /
`:status` columns are read from the PINNED boards and are NOT re-derived --
a reference verdict at a fixed budget on a fixed file does not change, and
re-running it would only add noise and cost.

    UFNIA   bench-results/tier1-divisions-headtohead-20260913/UFNIA.tsv  (ADR-1957)
    UFLIA   bench-results/six-divisions-headtohead-20260912/UFLIA.tsv    (ADR-1950)

Both pinned boards used the identical envelope this lane uses: 24 s wall,
8 GiB `ulimit -v`, one pinned physical core, z3 4.13.3 and cvc5 1.3.4.

`winnable` = we returned `unknown` and at least one reference decided.  It is
the census denominator, and it is written out so a reader can re-derive it.

ADR-1957: the disagreement count is published with the number of our verdicts
anything could compare against, per division, and the line says so when that
number is zero.
"""

import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent
PINNED = {
    "UFNIA": ROOT / "tier1-divisions-headtohead-20260913" / "UFNIA.tsv",
    "UFLIA": ROOT / "six-divisions-headtohead-20260912" / "UFLIA.tsv",
}
DECIDED = ("sat", "unsat")


def tsv(p):
    lines = p.read_text().rstrip("\n").split("\n")
    head = lines[0].split("\t")
    return [dict(zip(head, ln.split("\t"))) for ln in lines[1:]]


def main():
    rc = 0
    for div, pinned_path in PINNED.items():
        ours_path = HERE / "census" / f"{div}.tsv"
        if not ours_path.exists():
            print(f"== {div}: DID NOT RUN")
            rc = 1
            continue
        ours = {r["file"]: r for r in tsv(ours_path)}
        ref = {r["file"]: r for r in tsv(pinned_path)}
        common = [f for f in ref if f in ours]
        if len(common) != len(ref):
            print(f"ABORT {div}: our run covers {len(common)} of the pinned"
                  f" {len(ref)} rows")
            return 2

        we = sum(ours[f]["verdict"] in DECIDED for f in common)
        was = sum(ref[f]["axeyum"] in DECIDED for f in common)
        z3 = sum(ref[f]["z3"] in DECIDED for f in common)
        cvc5 = sum(ref[f]["cvc5"] in DECIDED for f in common)
        best = sum(ref[f]["z3"] in DECIDED or ref[f]["cvc5"] in DECIDED for f in common)
        winnable = [f for f in common
                    if ours[f]["verdict"] not in DECIDED
                    and (ref[f]["z3"] in DECIDED or ref[f]["cvc5"] in DECIDED)]

        print(f"== {div}  n={len(common)}")
        print(f"   axeyum (this lane) {we}    axeyum (pinned board) {was}"
              f"    z3 {z3}   cvc5 {cvc5}   best-ref {best}")
        print(f"   winnable (we unknown, a reference decided): {len(winnable)}")

        # ADR-1957: soundness, with the comparable denominator on the same line.
        agree_s = agree_z = agree_c = 0
        comp_s = comp_z = comp_c = 0
        disagree = []
        for f in common:
            v = ours[f]["verdict"]
            if v not in DECIDED:
                continue
            for key, dec in (("status", "s"), ("z3", "z"), ("cvc5", "c")):
                other = ref[f][key]
                if other not in DECIDED:
                    continue
                if dec == "s":
                    comp_s += 1
                elif dec == "z":
                    comp_z += 1
                else:
                    comp_c += 1
                if other == v:
                    if dec == "s":
                        agree_s += 1
                    elif dec == "z":
                        agree_z += 1
                    else:
                        agree_c += 1
                else:
                    disagree.append((f, v, key, other))
        comparable = comp_s + comp_z + comp_c
        tail = ("  <-- VACUOUS: nothing checked any verdict we produced"
                if comparable == 0 else "")
        print(f"   vs :status {agree_s}/{comp_s}   vs z3 {agree_z}/{comp_z}"
              f"   vs cvc5 {agree_c}/{comp_c}")
        print(f"   DISAGREEMENTS: {len(disagree)}{tail}")
        for d in disagree:
            print(f"      !! {d[0]} ours={d[1]} {d[2]}={d[3]}")
            rc = 3

        wf = HERE / "winnable" / f"{div}.txt"
        wf.parent.mkdir(exist_ok=True)
        wf.write_text("".join(f + "\n" for f in winnable))
        print(f"   winnable set written to {wf.relative_to(ROOT)}\n")
    return rc


if __name__ == "__main__":
    sys.exit(main())
