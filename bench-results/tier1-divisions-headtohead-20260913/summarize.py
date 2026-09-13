"""Board counts, the zero-disagreement check, and the winnable set, from the TSVs.

Run from this directory:  python3 summarize.py

Every number this prints is derived from the committed TSVs, so the table in
the README is re-derivable and is not a transcription.

It also prints the PROBE VERDICT for each division: the Tier-1 priority list
was built on a 24-file probe, and this compares that rate against n=200 with a
binomial 95 % interval around the probe, so "confirmed" and "refuted" are
decided by the arithmetic rather than by eye.
"""

import math
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
DIVS = ["AUFLIRA", "UFNIA", "ABV", "ALIA", "AUFNIRA", "AUFBV", "FP"]
DECIDED = {"sat", "unsat"}
# The Tier-1 priority list's probe: 24 files per division.
PROBE = {
    "AUFLIRA": 0.04, "UFNIA": 0.20, "ABV": 0.08, "ALIA": 0.00,
    "AUFNIRA": 0.04, "AUFBV": 0.04, "FP": 0.20,
}
PROBE_N = 24
POP = {
    "AUFLIRA": 20011, "UFNIA": 13464, "ABV": 4975, "ALIA": 3098,
    "AUFNIRA": 1480, "AUFBV": 1523, "FP": 2669,
}


def rows(div):
    p = HERE / f"{div}.tsv"
    if not p.exists():
        return None
    lines = p.read_text().rstrip("\n").split("\n")
    head = lines[0].split("\t")
    return [dict(zip(head, ln.split("\t"))) for ln in lines[1:]]


def wilson(k, n, z=1.96):
    """Wilson 95 % interval -- valid at k=0, which the normal interval is not.

    ALIA's probe was 0/24.  A normal-approximation interval there is the single
    point 0.0, which would make every possible board 'refute' it.  That would be
    an artifact of the wrong interval, not a finding.
    """
    if n == 0:
        return (0.0, 1.0)
    p = k / n
    d = 1 + z * z / n
    c = p + z * z / (2 * n)
    r = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n))
    return ((c - r) / d, (c + r) / d)


def main():
    winnable = {}
    tot = {"n": 0, "ax": 0, "z3": 0, "cv": 0, "win": 0}
    dis_all = 0
    comp_all = {"status": 0, "z3": 0, "cvc5": 0}
    verdicts = []
    for div in DIVS:
        rs = rows(div)
        if rs is None:
            # A board that DID NOT RUN must not render as a board with no
            # findings.  An absent row and a strong negative are different.
            print(f"== {div}: board DID NOT RUN")
            continue
        n = len(rs)
        ax = sum(r["axeyum"] in DECIDED for r in rs)
        z3 = sum(r["z3"] in DECIDED for r in rs)
        cv = sum(r["cvc5"] in DECIDED for r in rs)
        best = sum(r["z3"] in DECIDED or r["cvc5"] in DECIDED for r in rs)
        kills = {
            s: sum(r[f"{s}_k"] == "wrapper-killed" for r in rs)
            for s in ("ax", "z3", "cvc5")
        }
        rc134 = {
            s: sum(r[f"{s}_k"] == "rc134" for r in rs) for s in ("ax", "z3", "cvc5")
        }

        # Zero-disagreement: every verdict WE produce, against three checks.
        dis = []
        comp = {"status": 0, "z3": 0, "cvc5": 0}
        for r in rs:
            v = r["axeyum"]
            if v not in DECIDED:
                continue
            if r["status"] in DECIDED:
                comp["status"] += 1
                if r["status"] != v:
                    dis.append((r["file"], "status", r["status"], v))
            for s in ("z3", "cvc5"):
                if r[s] in DECIDED:
                    comp[s] += 1
                    if r[s] != v:
                        dis.append((r["file"], s, r[s], v))

        # Also flag reference-vs-reference and reference-vs-status conflicts,
        # which are not OUR wrong answer but invalidate the ground truth.
        ref_conflict = [
            r["file"]
            for r in rs
            if r["z3"] in DECIDED and r["cvc5"] in DECIDED and r["z3"] != r["cvc5"]
        ]
        ref_status = [
            (r["file"], s)
            for r in rs
            for s in ("z3", "cvc5")
            if r[s] in DECIDED and r["status"] in DECIDED and r[s] != r["status"]
        ]

        win = [
            r["file"]
            for r in rs
            if r["axeyum"] not in DECIDED
            and (r["z3"] in DECIDED or r["cvc5"] in DECIDED)
        ]
        winnable[div] = win

        lo, hi = wilson(round(PROBE[div] * PROBE_N), PROBE_N)
        rate = ax / n
        verdict = "CONFIRMED" if lo <= rate <= hi else "REFUTED"
        direction = "" if verdict == "CONFIRMED" else (
            " (board HIGHER)" if rate > hi else " (board LOWER)"
        )
        verdicts.append((div, PROBE[div], rate, lo, hi, verdict + direction))

        print(f"== {div} (n={n}, division has {POP[div]} files)")
        print(f"   axeyum {ax}  z3 {z3}  cvc5 {cv}   best-ref {best}")
        print(f"   wrapper-killed  {kills}")
        print(f"   rc134 (8GiB)    {rc134}")
        print(
            f"   comparable: status {comp['status']}  z3 {comp['z3']}  cvc5 {comp['cvc5']}"
        )
        # A zero-disagreement figure over verdicts nothing else checked is
        # worth nothing, and on THIS board that is not hypothetical: ALIA
        # produces no verdicts at all, and ABV declares `:status unknown` on
        # 199 of 200 files while both references return `unknown` on all four
        # rows we decide.  Both print "DISAGREEMENTS: 0" and neither zero means
        # what a reader will take it to mean, so the line says so itself rather
        # than leaving it to a footnote in a README nobody reads beside the TSV.
        ncomp = comp["status"] + comp["z3"] + comp["cvc5"]
        vac = "  <-- VACUOUS: nothing checked any verdict we produced" if (
            not ncomp and not dis) else ""
        print(f"   DISAGREEMENTS: {len(dis)}{vac}")
        for d in dis:
            print(f"     !! {d}")
        print(f"   reference-vs-reference conflicts: {len(ref_conflict)}")
        for f in ref_conflict:
            print(f"     ?? {f}")
        print(f"   reference-vs-:status conflicts: {len(ref_status)}")
        for f in ref_status[:5]:
            print(f"     ?s {f}")
        print(f"   winnable (we unknown, a reference decides): {len(win)}")
        print(f"   probe {PROBE[div]:.0%} (n=24, 95% CI {lo:.1%}-{hi:.1%})"
              f"  board {rate:.1%}  -> {verdict}{direction}")

        tot["n"] += n
        tot["ax"] += ax
        tot["z3"] += z3
        tot["cv"] += cv
        tot["win"] += len(win)
        dis_all += len(dis)
        for k in comp_all:
            comp_all[k] += comp[k]

    if tot["n"]:
        print(f"\nTOTAL over {tot['n']} files: axeyum {tot['ax']}"
              f" ({tot['ax'] / tot['n']:.1%})  z3 {tot['z3']}  cvc5 {tot['cv']}"
              f"  winnable {tot['win']}")
        print(f"DISAGREEMENTS TOTAL: {dis_all}   comparable: {comp_all}")
        print("\nprobe verdicts:")
        for div, p, rate, lo, hi, v in verdicts:
            print(f"  {div:9s} probe {p:5.0%} (CI {lo:5.1%}-{hi:5.1%})"
                  f"  board {rate:6.1%}  {v}")

    out = HERE / "winnable"
    out.mkdir(exist_ok=True)
    root = (
        "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"
    )
    for div, win in winnable.items():
        (out / f"{div}.txt").write_text(
            "".join(f"{root}{f}\n" for f in win)
        )
    print(f"\nwinnable lists written to {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
