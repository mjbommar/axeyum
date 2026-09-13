"""Pin the 200-file parity sample for QF_ABVFP / QF_BVFP / QF_UFBV.

Fixed stride THROUGH the division, spanning index 0 .. N-1 inclusive, so the
tail families are reachable.  A plain `N//200` integer stride stops at
199*(N//200), which for QF_UFBV is index 1393 of 1510 and silently drops the
last three families (107 files).  Even spacing over the full range does not.
"""

import pathlib
import subprocess

ROOT = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental"
OUT = pathlib.Path(
    "/home/mjbommar/projects/personal/axeyum/.claude/worktrees/"
    "agent-a73042a59304872a1/bench-results/parity-lists"
)
K = 200

for div in ["QF_ABVFP", "QF_BVFP", "QF_UFBV"]:
    r = subprocess.run(
        ["find", f"{ROOT}/{div}", "-name", "*.smt2"],
        capture_output=True, text=True, check=True,
    )
    files = sorted(r.stdout.split("\n")[:-1])
    n = len(files)
    assert n >= K, div
    idx = [round(i * (n - 1) / (K - 1)) for i in range(K)]
    assert len(set(idx)) == K, div
    sel = [files[i] for i in idx]
    (OUT / f"{div}.txt").write_text("\n".join(sel) + "\n")
    print(f"{div}\ttotal={n}\tstride={(n - 1) / (K - 1):.2f}\tk={len(sel)}\tspan={idx[0]}..{idx[-1]}")
