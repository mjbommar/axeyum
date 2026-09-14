"""Sample a QF_BV control population: up to 2 files per FAMILY, deterministically.

Not a prefix of a directory walk -- a locality-biased prefix of one family is
not a control for a division. Seeded so it is reproducible.
"""
import os, random, sys

root = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/QF_BV"
rng = random.Random(20300914)
picked = []
for fam in sorted(os.listdir(root)):
    famdir = os.path.join(root, fam)
    if not os.path.isdir(famdir):
        continue
    files = []
    for dirpath, _dirnames, filenames in os.walk(famdir):
        for fn in filenames:
            if fn.endswith(".smt2"):
                p = os.path.join(dirpath, fn)
                try:
                    if os.path.getsize(p) < 200_000:
                        files.append(p)
                except OSError:
                    pass
        if len(files) > 400:
            break
    if not files:
        continue
    files.sort()
    for p in rng.sample(files, min(2, len(files))):
        picked.append(p.split("/non-incremental/")[-1])

picked.sort()
with open(sys.argv[1], "w") as fh:
    fh.write("\n".join(picked) + "\n")
print(f"{len(picked)} files over {len({p.split('/')[1] for p in picked})} families")
