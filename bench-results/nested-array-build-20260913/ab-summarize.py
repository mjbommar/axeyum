"""Summarize the interleaved A/B, and check every moved verdict three ways.

Reads the per-division TSVs written by `ab-run.sh` and prints:

  1. the board line -- baseline decided / lane decided / moved / REGRESSED;
  2. the agreement check on every verdict the lane produces: against the
     benchmark's declared `:status`, and (with `--refs`) against z3 and cvc5
     re-run at the same budget.

A REGRESSION -- a file the baseline decided and the lane does not -- is printed
per file, not summarized, because one is enough to stop a merge.

Run from this directory:
    python3 ab-summarize.py [<ab dir>] [--refs] [--budget N]
"""

import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
DIVS = ["AUFLIRA", "AUFNIRA", "ALIA", "ABV", "QF_ABV", "QF_BV"]
CONTROLS = {"QF_ABV", "QF_BV"}
Z3 = "/usr/bin/z3"
CVC5 = "/nas3/data/axeyum/harness/bin/cvc5"


def reference(binary, args, path, budget):
    try:
        out = subprocess.run(
            [binary, *args, path],
            capture_output=True,
            text=True,
            timeout=budget * 2 + 10,
        ).stdout
    except (subprocess.TimeoutExpired, OSError):
        return "error"
    for line in out.splitlines():
        if line.strip() in ("sat", "unsat", "unknown"):
            return line.strip()
    return "error"


def main(argv):
    ab = HERE / "ab"
    refs = "--refs" in argv
    budget = 24
    positional = [a for a in argv[1:] if not a.startswith("--")]
    if positional:
        ab = pathlib.Path(positional[0])
    if "--budget" in argv:
        budget = int(argv[argv.index("--budget") + 1])

    hdr = (f"{'division':9s} {'files':>6s} {'base':>6s} {'lane':>6s} {'moved':>6s}"
           f" {'REGRESSED':>10s}")
    print(hdr)
    print("-" * len(hdr))
    regressions, disagreements, moved_files = [], [], []
    for div in DIVS:
        path = ab / f"{div}.tsv"
        if not path.exists():
            print(f"{div:9s} {'DID NOT RUN':>6s}")
            continue
        n = base = lane = moved = regressed = 0
        with open(path) as fh:
            next(fh)
            for line in fh:
                c = line.rstrip("\n").split("\t")
                if len(c) < 6:
                    continue
                n += 1
                f, b, l, st = c[0], c[1], c[3], c[5]
                base += b != "unknown"
                lane += l != "unknown"
                if b == "unknown" and l != "unknown":
                    moved += 1
                    moved_files.append((div, f, l, st))
                if b != "unknown" and l == "unknown":
                    regressed += 1
                    regressions.append((div, f, b))
                # The cheapest check there is, and it runs on every row:
                # two verdicts that differ, or a verdict contradicting the
                # benchmark's own declared status.
                if b != "unknown" and l != "unknown" and b != l:
                    disagreements.append((div, f, f"base={b}", f"lane={l}"))
                for who, v in (("base", b), ("lane", l)):
                    if v in ("sat", "unsat") and st in ("sat", "unsat") and v != st:
                        disagreements.append((div, f, f"{who}={v}", f":status={st}"))
        tag = f"{div}*" if div in CONTROLS else div
        print(f"{tag:9s} {n:6d} {base:6d} {lane:6d} {moved:6d} {regressed:10d}")

    print("-" * len(hdr))
    print("* control division -- ADR-1965 touches `ArraySortKey::to_sort`,")
    print("  `Sort::array_sorts` and `Features::note_sort`, which EVERY flat")
    print("  array query goes through, so a regression there would be invisible")
    print("  in the four divisions this lane is aimed at.")
    print()

    if regressions:
        print(f"REGRESSIONS ({len(regressions)}) -- baseline decided, lane does not:")
        for row in regressions:
            print(f"  {row}")
    else:
        print("REGRESSIONS: none.")

    if disagreements:
        print(f"DISAGREEMENTS ({len(disagreements)}):")
        for row in disagreements:
            print(f"  {row}")
    else:
        print("DISAGREEMENTS (arm-vs-arm and verdict-vs-:status): none.")

    if not refs:
        print()
        print(f"reference cross-check on {len(moved_files)} moved files: NOT RUN")
        print("  (pass --refs to re-run z3 and cvc5 on each)")
        return 1 if (regressions or disagreements) else 0

    print()
    print(f"reference cross-check on {len(moved_files)} moved files "
          f"(z3 -T:{budget}, cvc5 --tlimit={budget * 1000}):")
    agree = {"z3": 0, "cvc5": 0}
    empty = {"z3": 0, "cvc5": 0}
    contra = []
    for div, f, verdict, st in moved_files:
        z = reference(Z3, [f"-T:{budget}"], f, budget)
        c = reference(CVC5, [f"--tlimit={budget * 1000}"], f, budget)
        for who, v in (("z3", z), ("cvc5", c)):
            if v == verdict:
                agree[who] += 1
            elif v in ("unknown", "error"):
                empty[who] += 1
            else:
                contra.append((div, f, verdict, who, v))
    total = len(moved_files)
    for who in ("z3", "cvc5"):
        print(f"  {who:5s} agrees {agree[who]:4d} / {total}, "
              f"no opinion {empty[who]:4d}, CONTRADICTS "
              f"{total - agree[who] - empty[who]}")
    if contra:
        print("  CONTRADICTIONS:")
        for row in contra:
            print(f"    {row}")
        return 1
    print("  no reference contradicts a moved verdict.")
    return 1 if (regressions or disagreements) else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
