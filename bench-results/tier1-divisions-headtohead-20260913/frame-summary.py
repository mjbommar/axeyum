"""Derive this board's reference-frame claim from `loadframe.tsv`, rather than
asserting it.

board-six could write "foreign pinned jobs were ZERO in every one of 363
samples".  This lane cannot: two other lanes (`quant-rounds`, `nested-array-ir`)
ran pinned work on the same boxes for the whole measurement, and the very first
launch collided with them.  So the claim here is narrower and has to be checked
rather than asserted:

    no job outside this lane ever held a PHYSICAL CORE this board was using.

`loadframe.tsv`'s `foreign_cores` column lists every pin spec on the box that is
not one of the ORIGINAL two (5,13 and 6,14).  After the board was re-balanced
across eight cores, this lane's OWN extra shards appear in that column -- so the
column cannot be read directly and the `overlap` flag, which only tests the
original two, is no longer sufficient either.  This script subtracts the specs
this lane is known to have used and checks what is left.

MINE is the set of pin specs this lane launched, and it is the one input that is
declared rather than measured.  It is checked against the committed scripts: a
spec used by a launcher and missing here would make the residue look foreign and
the check would FAIL LOUDLY rather than pass.  That is the safe direction.

Run from this directory:  python3 frame-summary.py
"""

import collections
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
# Overridable so controls/frame-control.sh can point it at fixtures whose
# answers are known.  A "FRAME OK" that cannot print "FRAME VIOLATED" is not a
# frame check, and this script's violation branch is otherwise unreachable on a
# clean run -- which is every run that gets published.
TSV = pathlib.Path(
    sys.argv[1] if len(sys.argv) > 1
    else "/nas3/data/axeyum/harness/tier1-divisions/out/loadframe.tsv"
)
# Every pin spec this lane launched, across the whole run.
MINE = {"5,13", "6,14", "1,9", "7,15", "3,11"}
MY_CORES = {int(c) % 8 for spec in MINE for c in spec.split(",")}


def main():
    if not TSV.exists():
        print(f"loadframe DID NOT RUN ({TSV} missing)")
        return 1
    lines = TSV.read_text().rstrip("\n").split("\n")
    head = lines[0].split("\t")
    rows = [dict(zip(head, ln.split("\t"))) for ln in lines[1:]]
    if not rows:
        print("loadframe RAN BUT RECORDED NOTHING -- not the same as a clean frame")
        return 1

    print(f"this board used PHYSICAL cores {sorted(MY_CORES)}"
          f" (pin specs {sorted(MINE)})")
    print(f"{len(rows)} samples over {len({r['host'] for r in rows})} hosts\n")

    residue = collections.Counter()
    bad = []
    for r in rows:
        specs = [s for s in r["foreign_cores"].split(";") if s and s != "-"]
        for s in specs:
            if s in MINE:
                continue
            residue[s] += 1
            for c in s.split(","):
                if "-" in c:          # a range: cannot be tested by membership
                    bad.append((r["ts"], r["host"], s, "RANGE"))
                elif int(c) % 8 in MY_CORES:
                    bad.append((r["ts"], r["host"], s, f"core {int(c) % 8}"))

    def cores_of(spec):
        """Physical cores of a pin spec, or None when it cannot be resolved.

        A RANGE spec (`0-7`) is not resolvable by membership.  The first version
        of this code assumed every token was an integer and raised ValueError on
        the range fixture -- which aborted the script AFTER the violation had
        been recorded but BEFORE it was printed, so the control saw a non-zero
        exit with no finding in it.  An exit status without the finding is the
        failure mode this whole directory exists to prevent.
        """
        try:
            return sorted({int(x) % 8 for x in spec.split(",")})
        except ValueError:
            return None

    print("pin specs seen that are NOT this lane's, with sample counts:")
    for s, c in residue.most_common():
        cs = cores_of(s)
        print(f"   {c:4d}  {s}   -> physical core(s)"
              f" {cs if cs is not None else 'UNRESOLVABLE (range)'}")

    loads = collections.defaultdict(list)
    for r in rows:
        try:
            loads[r["host"]].append(float(r["load1"]))
        except ValueError:
            pass
    print("\nload1 range per host:")
    for h in sorted(loads):
        v = sorted(loads[h])
        print(f"   {h}  {v[0]:.2f} - {v[-1]:.2f}   (median {v[len(v) // 2]:.2f})")

    print()
    if bad:
        print(f"!! FRAME VIOLATED: {len(bad)} sample(s) show a foreign pin on a"
              f" core this board used")
        for b in bad[:10]:
            print(f"   {b}")
        return 1
    used = sorted({c for s in residue for c in (cores_of(s) or [])})
    print(f"FRAME OK: in all {len(rows)} samples, every pin that is not this"
          f" lane's held a physical core this board never used ({used}).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
