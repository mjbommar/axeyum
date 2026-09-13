"""Pin the 200-file parity sample for the four unmeasured A-divisions.

FULL-SPAN spacing over index 0 .. N-1 inclusive, so the tail families are
reachable.  NOT the plain `N//200` integer stride: that stops at 199*(N//200)
and never reaches the tail.  BOARD-FPBV measured that on QF_UFBV the stride
stops at index 1393 of 1510 and drops the last three families (107 files, 7 %
of the division) in which we score 0 of 15 -- so the obvious stride would have
hidden a real hole.

Run from the lane worktree.  Writes bench-results/parity-lists/<DIV>.txt.
These lists are committed BEFORE anything is measured; that commit is what
makes the board rows non-cherry-picked.
"""

import pathlib
import subprocess

ROOT = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental"
OUT = pathlib.Path(__file__).resolve().parent.parent / "parity-lists"
K = 200
DIVISIONS = ["AUFLIRA", "ABV", "ALIA", "AUFNIRA"]


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    for div in DIVISIONS:
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
        (OUT / f"{div}.txt").write_text("\n".join(sel) + "\n")

        # Family coverage of the sample against the division, reported so the
        # span claim is checkable rather than asserted.
        def fam(p):
            return p[len(ROOT) + len(div) + 2:].split("/")[0]

        all_f = sorted({fam(f) for f in files})
        sel_f = sorted({fam(f) for f in sel})
        print(
            f"{div:12s} total={n:6d} stride={(n - 1) / (K - 1):8.2f} "
            f"k={len(sel)} span={idx[0]}..{idx[-1]} "
            f"families={len(sel_f)}/{len(all_f)}"
        )
        missed = [f for f in all_f if f not in sel_f]
        if missed:
            sizes = {f: sum(1 for x in files if fam(x) == f) for f in missed}
            print(f"             families not sampled: "
                  f"{sorted(sizes.items(), key=lambda kv: -kv[1])}")


if __name__ == "__main__":
    main()
