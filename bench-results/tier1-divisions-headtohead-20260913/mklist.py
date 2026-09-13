"""Pin the 200-file parity sample for the seven Tier-1 divisions.

FULL-SPAN spacing over index 0 .. N-1 inclusive, so the tail families are
reachable.  NOT the plain `N//200` integer stride: that stops at 199*(N//200)
and never reaches the tail.  BOARD-FPBV measured that on QF_UFBV the stride
stops at index 1393 of 1510 and drops the last three families in which we score
0 of 15.

FP IS A SPECIAL CASE AND ITS LIST HAS A DIFFERENT NAME.
`bench-results/parity-lists/FP.txt` ALREADY EXISTS and was built with the PLAIN
INTEGER STRIDE -- verified here, not assumed: it matches
`[files[i*(n//200)] for i in range(200)]` exactly and does NOT match the
full-span spacing.  It stops at index 2587 of 2668.  Other lanes' committed
artifacts reference that file by name, so overwriting it would retroactively
change what those boards say they measured.  This lane writes the protocol-
conformant list to `FP-fullspan.txt` and leaves the stride list alone.

Run from the lane worktree.  Writes bench-results/parity-lists/<STEM>.txt.
These lists are committed BEFORE anything is measured; that commit is what
makes the board rows non-cherry-picked.
"""

import pathlib
import subprocess
import sys

ROOT = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental"
OUT = pathlib.Path(__file__).resolve().parent.parent / "parity-lists"
K = 200
# (division, output stem)
DIVISIONS = [
    ("AUFLIRA", "AUFLIRA"),
    ("UFNIA", "UFNIA"),
    ("ABV", "ABV"),
    ("ALIA", "ALIA"),
    ("AUFNIRA", "AUFNIRA"),
    ("AUFBV", "AUFBV"),
    ("FP", "FP-fullspan"),
]


def main(dry=False):
    """dry=True prints the family-coverage table and writes nothing.

    The lists are pinned once and this script then REFUSES to re-pin, which is
    what protects them -- but it also made the family-coverage table in
    `findings/README.md` a transcription with no way to re-derive it.  `--dry-run`
    is that way.
    """
    for div, stem in DIVISIONS:
        r = subprocess.run(
            ["find", f"{ROOT}/{div}", "-name", "*.smt2"],
            capture_output=True, text=True, check=True,
        )
        files = sorted(r.stdout.split("\n")[:-1])
        n = len(files)
        assert n >= K, f"{div}: only {n} files"
        idx = [round(i * (n - 1) / (K - 1)) for i in range(K)]
        assert len(set(idx)) == K, div
        assert idx[0] == 0 and idx[-1] == n - 1, div
        sel = [files[i] for i in idx]

        # Guard the FP special case rather than trusting the comment above.
        stride = [files[i * (n // K)] for i in range(K)]
        if dry:
            # Re-derive the committed list and say whether it still matches.
            # This is what makes "these rows are not cherry-picked" checkable
            # AFTER the fact: the lists were committed at 3320c7136 before
            # anything was measured, and this says they are still exactly what
            # the construction above produces.
            q = OUT / f"{stem}.txt"
            if q.exists():
                have = q.read_text().rstrip("\n").split("\n")
                verdict = ("MATCHES the full-span construction"
                           if have == sel else "!! DIFFERS")
                print(f"{stem:12s} committed list: {verdict}")
            else:
                print(f"{stem:12s} committed list: ABSENT")
        elif stem != div:
            assert (OUT / f"{div}.txt").exists(), f"{div}: renamed but no clash"
            prior = (OUT / f"{div}.txt").read_text().rstrip("\n").split("\n")
            assert prior == stride, f"{div}.txt is not the stride list after all"
            assert prior != sel, f"{div}.txt already IS the full-span list"
        else:
            assert not (OUT / f"{stem}.txt").exists(), f"{stem}.txt already exists"

        if not dry:
            (OUT / f"{stem}.txt").write_text("\n".join(sel) + "\n")

        # Family coverage of the sample against the division, reported so the
        # span claim is checkable rather than asserted.  Also report what the
        # plain stride WOULD have reached, which is the point of the protocol.
        def fam(p):
            return p[len(ROOT) + len(div) + 2:].split("/")[0]

        all_f = sorted({fam(f) for f in files})
        sel_f = sorted({fam(f) for f in sel})
        str_f = sorted({fam(f) for f in stride})
        print(
            f"{div:10s} -> {stem:12s} total={n:6d} step={(n - 1) / (K - 1):8.2f} "
            f"k={len(sel)} span={idx[0]}..{idx[-1]} "
            f"families={len(sel_f)}/{len(all_f)}  "
            f"(plain stride would stop at index {199 * (n // K)} "
            f"and reach {len(str_f)}/{len(all_f)} families)"
        )
        missed = [f for f in all_f if f not in sel_f]
        if missed:
            sizes = {f: sum(1 for x in files if fam(x) == f) for f in missed}
            print(f"             families not sampled: "
                  f"{sorted(sizes.items(), key=lambda kv: -kv[1])}")


if __name__ == "__main__":
    main(dry="--dry-run" in sys.argv)
