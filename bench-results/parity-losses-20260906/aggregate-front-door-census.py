import sys
from collections import defaultdict

tsv = sys.argv[1]
rows = [l.rstrip("\n").split("\t") for l in open(tsv)]
hdr = rows[0]
rows = [dict(zip(hdr, r)) for r in rows[1:]]

tot = defaultdict(float)
wall = 0.0
for r in rows:
    wall += int(r["wall_ms"])
    for part in r["ladder_stage_costs"].split("|"):
        if not part:
            continue
        k, v = part.rsplit("=", 1)
        tot[k] += float(v.rstrip("ms"))

print("total wall over %d files: %.1f s" % (len(rows), wall / 1000))
print("%-24s %10s %8s" % ("stage", "seconds", "share"))
for k, v in sorted(tot.items(), key=lambda kv: -kv[1]):
    print("%-24s %10.1f %7.1f%%" % (k, v / 1000, 100 * v / wall))
fmf = tot.get("uf-fmf-probe", 0) + tot.get("uf-fmf-full", 0)
print("\nfinite model finding (probe+full): %.1f s = %.1f%% of the wall" % (fmf / 1000, 100 * fmf / wall))
ref = tot.get("egraph", 0) + tot.get("mbqi", 0) + tot.get("mbqi-quick", 0)
print("refutation family (mbqi-quick+egraph+mbqi): %.1f s = %.1f%%" % (ref / 1000, 100 * ref / wall))

print("\n== overshoot past the 24 s budget")
over = [(int(r["wall_ms"]), r["file"], r["budget_stage"]) for r in rows if int(r["wall_ms"]) > 26000]
for w, f, s in sorted(over, reverse=True):
    print("  %6d ms  %-46s dominant=%s" % (w, f[:46], s))
print("  %d of %d files exceed 26 s; max %d ms" % (len(over), len(rows), max(int(r["wall_ms"]) for r in rows)))

print("\n== budget left unspent (wall < 20 s)")
un = [(int(r["wall_ms"]), r["file"], r["class"]) for r in rows if int(r["wall_ms"]) < 20000]
for w, f, c in sorted(un):
    print("  %6d ms  %-46s %s" % (w, f[:46], c))

print("\n== e-graph ground cap")
cap = sum(1 for r in rows if r["egraph_max_ground"] == "8192")
print("  reached MAX_GROUND_TERMS=8192 on %d of %d files" % (cap, len(rows)))
print("  max rounds: %s" % sorted((int(r["egraph_max_round"]) for r in rows), reverse=True)[:8])
