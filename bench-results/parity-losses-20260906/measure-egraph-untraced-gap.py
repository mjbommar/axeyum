import os
import re

QT = re.compile(r"^\[qtrace\] (\S+) \+([0-9.]+)s (.*)$")
CUM = {"forall-exists-witness", "finite-expansion", "uf-fmf-probe", "egraph", "mbqi", "uf-fmf-full"}
LOC = {"mbqi-quick", "nat-induction"}

rows = [l.rstrip("\n").split("\t") for l in open("UF.front-door.census.tsv")]
h = rows[0]
rows = [dict(zip(h, r)) for r in rows[1:]]

print(
    "%-46s %10s %10s %10s %8s"
    % ("file", "egraph_ms", "seg_traced", "UNTRACED", "last_gnd")
)
for i, r in enumerate(rows, 1):
    if r["class"] != "search-timeout":
        continue
    txt = open(os.path.join("run", "%d.err" % i), errors="replace").read()
    acc = 0.0
    seg = 0.0
    segwin = 0.0
    egraph_cost = None
    lastg = 0
    for line in txt.splitlines():
        m = QT.match(line.strip())
        if not m:
            continue
        n = m.group(1)
        ms = float(m.group(2)) * 1000
        note = m.group(3)
        if n in CUM:
            cost = ms - acc
            acc = ms
            if n == "egraph":
                egraph_cost = cost
                segwin = seg
            seg = 0.0
        elif n in LOC:
            acc += ms
            seg = 0.0
        else:
            g = re.search(r"ground=(\d+)", note)
            if g:
                lastg = int(g.group(1))
            if note not in ("closed-universal done", "targeted done"):
                seg += ms
    if egraph_cost is None:
        print("%-46s  no egraph checkpoint" % r["file"][:46])
        continue
    print(
        "%-46s %10.0f %10.0f %10.0f %8d"
        % (r["file"][:46], egraph_cost, segwin, egraph_cost - segwin, lastg)
    )
