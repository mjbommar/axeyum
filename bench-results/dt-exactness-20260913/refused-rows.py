#!/usr/bin/env python3
import csv, collections, sys
base = "bench-results/ufdt-family-20260913/census"
out = "/tmp/claude-1000/-home-mjbommar-projects-personal-axeyum/b5abceb2-1e55-4606-b944-34c43c75096d/scratchpad/dt-exactness"
pats = {
    "arg1935": "congruence over a datatype argument whose expansion is not exact",
    "res1946": "RESULT datatype's expansion is not exact",
    "nonatomic1942": "applied to a datatype term that is neither a free variable",
}
tot = collections.Counter()
rows = collections.defaultdict(list)
for div in ["UFDTLIRA", "UFDT", "AUFDTLIRA", "UFDTNIRA"]:
    with open(f"{base}/{div}.winnable.tsv") as f:
        for row in csv.DictReader(f, delimiter="\t"):
            g = row.get("giveup", "") or ""
            for k, pat in pats.items():
                if pat in g:
                    tot[(div, k)] += 1
                    rows[div].append((row["file"], k, row.get("wall_ms"), row.get("verdict"), row.get("deepest"), row.get("bound_by")))
for div in ["UFDTLIRA", "UFDT", "AUFDTLIRA", "UFDTNIRA"]:
    print(div, {k[1]: v for k, v in tot.items() if k[0] == div}, "sum", sum(v for k, v in tot.items() if k[0] == div))
    with open(f"{out}/{div}.refused.tsv", "w") as f:
        for t in rows[div]:
            f.write("\t".join("" if x is None else str(x) for x in t) + "\n")
print("TOTAL", sum(tot.values()))
