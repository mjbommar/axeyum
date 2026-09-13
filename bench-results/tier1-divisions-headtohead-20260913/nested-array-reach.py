"""Size the nested-array parse refusal the way a lane deciding whether to BUILD
should see it, from the committed boards and censuses.

The brief for this lane names a **29,564-file** figure that the `NESTED-ARRAY-IR`
lane is sizing against.  That number is exactly

    AUFLIRA 20,011 + ABV 4,975 + ALIA 3,098 + AUFNIRA 1,480 = 29,564

i.e. the WHOLE POPULATION of the four array divisions.  It is a population, not
a reach, and it overstates what the change can touch in two independent ways
that this script separates:

  1. **Not every file in those divisions is refused.**  The census measures the
     refusal share of the WINNABLE set, and the board measures how much of the
     division is winnable at all.
  2. **Not every refused file is winnable.**  A file that we refuse AND both
     references also fail is not a file the change wins; it is a file nobody
     decides.  `winnable` is defined as "we returned unknown and a reference
     decided", so it is already the right denominator.

And one way it overstates that NO arithmetic here can fix, which the output
prints rather than leaves implied:

  3. **Parsing a file is not deciding it.**  The census says the FRONT DOOR
     refuses; it says nothing about whether the solver behind it would decide
     the query.  Every number below is a CEILING on the change's reach, not a
     prediction of files gained.

Run from this directory:  python3 nested-array-reach.py
"""

import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
# The four divisions behind the 29,564 figure, with their on-disk populations.
ARRAY_DIVS = {"AUFLIRA": 20011, "ABV": 4975, "ALIA": 3098, "AUFNIRA": 1480}
SAMPLE = 200
NESTED = "nested array element sort is unsupported"


def main():
    print(f"the brief's figure: {sum(ARRAY_DIVS.values()):,} files"
          f" = the whole population of {', '.join(ARRAY_DIVS)}\n")
    hdr = (f"{'division':9s} {'on disk':>8s} {'sampled':>8s} {'winnable':>9s}"
           f" {'nested':>7s} {'of winn':>8s} {'of sample':>10s}"
           f" {'projected ceiling':>18s}")
    print(hdr)
    print("-" * len(hdr))
    tot_proj, tot_pop, missing = 0, 0, []
    for div, pop in ARRAY_DIVS.items():
        cp = HERE / "census" / f"{div}.tsv"
        wp = HERE / "winnable" / f"{div}.txt"
        if not cp.exists() or not wp.exists():
            missing.append(div)
            print(f"{div:9s} {pop:8,d} {'-':>8s} {'DID NOT RUN':>9s}")
            continue
        win = len([x for x in wp.read_text().split("\n") if x])
        rows = cp.read_text().rstrip("\n").split("\n")[1:]
        nested = sum(1 for r in rows if NESTED in r)
        # Share OF THE SAMPLE is the one that projects: the sample is 200 of the
        # division, so nested/200 estimates the division-wide rate directly.
        # nested/winnable is the census share and does NOT project, because
        # `winnable` is itself a measured fraction of the sample.
        proj = round(nested / SAMPLE * pop)
        tot_proj += proj
        tot_pop += pop
        print(f"{div:9s} {pop:8,d} {SAMPLE:8d} {win:9d} {nested:7d}"
              f" {nested / win:7.0%} {nested / SAMPLE:10.1%} {proj:18,d}")
    print("-" * len(hdr))
    if missing:
        print(f"!! census DID NOT RUN for {', '.join(missing)} -- the total below"
              f" covers only {tot_pop:,} of {sum(ARRAY_DIVS.values()):,} files"
              f" and is a PARTIAL figure")
    print(f"{'TOTAL':9s} {tot_pop:8,d} {'':>8s} {'':>9s} {'':>7s} {'':>8s}"
          f" {'':>10s} {tot_proj:18,d}")
    print(f"\nprojected CEILING {tot_proj:,} of the brief's"
          f" {sum(ARRAY_DIVS.values()):,} "
          f"({tot_proj / sum(ARRAY_DIVS.values()):.0%})")
    print("\nCEILING, not a forecast: the census says the FRONT DOOR refuses the")
    print("file.  Whether the solver behind it would decide the query is not")
    print("measured here and cannot be inferred from these rows.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
