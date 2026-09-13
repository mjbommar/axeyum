"""Summarize the array-free surrogate sweep, and check its soundness claim.

Reads the per-division TSVs written by `surrogate-sweep.sh` and the board's own
TSVs from `tier1-divisions-headtohead-20260913`, and prints:

  1. the surrogate REACH per division -- how many winnable files axeyum decides
     on the surrogate, `unsat` only, because only `unsat` transfers;
  2. the SOUNDNESS CHECK on the rewrite itself: a surrogate `unsat` on a file
     whose original is `sat` would refute the transfer argument.  z3's column is
     the independent arm of that check.

Run from this directory:  python3 surrogate-summarize.py [<sweep dir>]
"""

import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
BOARD = HERE / ".." / "tier1-divisions-headtohead-20260913"
DIVS = ["AUFLIRA", "AUFNIRA", "ALIA", "ABV"]
# ADR-1957's projected per-division ceiling (nested share of winnable x on disk).
CEILING = {"AUFLIRA": 18510, "AUFNIRA": 955, "ALIA": 511, "ABV": 423}


def board_rows(div):
    """file -> (axeyum, z3, cvc5, declared status) from the committed board."""
    path = BOARD / f"{div}.tsv"
    out = {}
    with open(path) as fh:
        next(fh)
        for line in fh:
            c = line.rstrip("\n").split("\t")
            if len(c) < 11:
                continue
            out[c[0]] = (c[1], c[4], c[7], c[10])
    return out


def main(argv):
    sweep = pathlib.Path(argv[1]) if len(argv) > 1 else HERE / "sweep"
    root = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"

    hdr = (f"{'division':9s} {'winnable':>8s} {'rewritten':>9s} {'refused':>7s}"
           f" {'ax unsat':>8s} {'ax sat*':>7s} {'z3 unsat':>8s}"
           f" {'reach':>7s} {'ceiling':>8s} {'projected':>9s}")
    print(hdr)
    print("-" * len(hdr))

    tot = {k: 0 for k in ("win", "rw", "ref", "axu", "axs", "z3u", "proj")}
    unsound = []
    for div in DIVS:
        path = sweep / f"{div}.tsv"
        if not path.exists():
            print(f"{div:9s} {'DID NOT RUN':>8s}")
            continue
        board = board_rows(div)
        win = rw = ref = axu = axs = z3u = 0
        with open(path) as fh:
            next(fh)
            for line in fh:
                c = line.rstrip("\n").split("\t")
                win += 1
                rel = c[0][len(root):] if c[0].startswith(root) else c[0]
                if c[1] == "REFUSED":
                    ref += 1
                    continue
                rw += 1
                ax, z3 = c[2], c[4]
                if ax == "unsat":
                    axu += 1
                if ax == "sat":
                    axs += 1
                if z3 == "unsat":
                    z3u += 1
                # The soundness check: a surrogate `unsat` whose ORIGINAL is
                # known `sat` refutes the transfer argument.  Both arms count.
                declared = board.get(rel, ("", "", "", ""))[3]
                z3_orig = board.get(rel, ("", "", "", ""))[1]
                for who, verdict in (("axeyum", ax), ("z3", z3)):
                    if verdict == "unsat" and (declared == "sat" or z3_orig == "sat"):
                        unsound.append((div, rel, who, declared, z3_orig))
        reach = axu / rw if rw else 0.0
        proj = round(CEILING[div] * reach)
        print(f"{div:9s} {win:8d} {rw:9d} {ref:7d} {axu:8d} {axs:7d} {z3u:8d}"
              f" {reach:6.1%} {CEILING[div]:8,d} {proj:9,d}")
        tot["win"] += win
        tot["rw"] += rw
        tot["ref"] += ref
        tot["axu"] += axu
        tot["axs"] += axs
        tot["z3u"] += z3u
        tot["proj"] += proj

    print("-" * len(hdr))
    overall = tot["axu"] / tot["rw"] if tot["rw"] else 0.0
    print(f"{'TOTAL':9s} {tot['win']:8d} {tot['rw']:9d} {tot['ref']:7d}"
          f" {tot['axu']:8d} {tot['axs']:7d} {tot['z3u']:8d}"
          f" {overall:6.1%} {sum(CEILING.values()):8,d} {tot['proj']:9,d}")

    print()
    print("* `ax sat` on a surrogate transfers NOTHING -- the rewrite deletes")
    print("  axioms, so only `unsat` carries back to the original.  The column")
    print("  is printed so the reach is not read as a decide rate.")
    print()
    if unsound:
        print(f"SOUNDNESS CHECK **FAILED**: {len(unsound)} surrogate `unsat` on a "
              f"file whose original is `sat`:")
        for row in unsound[:20]:
            print(f"  {row}")
        return 1
    print("SOUNDNESS CHECK passed: no surrogate `unsat` on a file whose original")
    print(f"  is `sat` ({tot['axu']} axeyum + {tot['z3u']} z3 surrogate refutations")
    print("  checked against the board's declared status and z3's own verdict).")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
