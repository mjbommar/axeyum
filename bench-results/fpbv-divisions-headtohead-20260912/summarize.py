"""Board counts, the zero-disagreement check, and the winnable set, from the TSVs.

Run from this directory:  python3 summarize.py

Every number this prints is derived from the committed TSVs, so the table in
the README is re-derivable and is not a transcription.
"""

import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
DIVS = ["QF_ABVFP", "QF_BVFP", "QF_UFBV"]
DECIDED = {"sat", "unsat"}


def rows(div):
    p = HERE / f"{div}.tsv"
    if not p.exists():
        return None
    lines = p.read_text().rstrip("\n").split("\n")
    head = lines[0].split("\t")
    return [dict(zip(head, ln.split("\t"))) for ln in lines[1:]]


def main():
    winnable = {}
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

        win = [
            r["file"]
            for r in rs
            if r["axeyum"] not in DECIDED
            and (r["z3"] in DECIDED or r["cvc5"] in DECIDED)
        ]
        winnable[div] = win

        print(f"== {div} (n={n})")
        print(f"   axeyum {ax}  z3 {z3}  cvc5 {cv}")
        print(f"   wrapper-killed  {kills}")
        print(f"   rc134 (8GiB)    {rc134}")
        print(
            f"   comparable: status {comp['status']}  z3 {comp['z3']}  cvc5 {comp['cvc5']}"
        )
        print(f"   DISAGREEMENTS: {len(dis)}")
        for d in dis:
            print(f"     !! {d}")
        print(f"   reference-vs-reference conflicts: {len(ref_conflict)}")
        for f in ref_conflict:
            print(f"     ?? {f}")
        print(f"   winnable (we unknown, a reference decides): {len(win)}")

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
