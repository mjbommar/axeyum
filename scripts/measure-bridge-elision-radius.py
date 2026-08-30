#!/usr/bin/env python3
"""Blast radius, read from the committed bridge_provenance block."""
import json, pathlib, collections

ROOT = pathlib.Path(__file__).resolve().parents[1]
A = ROOT / "artifacts" / "autogenesis"
CAT = json.loads((A / "mathlib-nat-int-fact-catalog-v1.json").read_text())
CACHE = json.loads((A / "mathlib-statement-constants-v1.json").read_text())["constants"]
ENV = set(json.loads((A / "kernel-environment-snapshot-v1.json").read_text())["declarations"])
VOC = json.loads((A / "mathlib-statable-vocabulary-v1.json").read_text())
PROV = VOC["bridge_provenance"]
SETTLED = {"proved", "refuted", "computed"}

facts = {}
for p in sorted((ROOT / "artifacts" / "facts").glob("*.json")):
    f = json.loads(p.read_text())
    if isinstance(f.get("id"), str):
        facts[f["id"]] = f
catalog = {r["source_name"]: r["fact_id"] for r in CAT["facts"]
           if isinstance(r, dict) and r.get("kind") == "external-source"}
settled = {n for n, i in catalog.items()
           if facts.get(i, {}).get("epistemic_status") in SETTLED}
bridge = set(VOC["bridge"])
tiers = collections.defaultdict(set)
for c, v in PROV.items():
    tiers[v["class"]].add(c)

print("bridge tiers:", {k: len(v) for k, v in sorted(tiers.items())},
      "total", sum(len(v) for v in tiers.values()), "of", len(bridge))

print("\n-- ELIDED, with witness counts (the promotion evidence) --")
for c in sorted(tiers["elided"]):
    print(f"   {c:16s} witnesses={PROV[c]['witnesses']:3d} "
          f"rendered={PROV[c]['rendered_witnesses']:3d}")

open_names = sorted(n for n in catalog if n not in settled)


def statable(adm):
    return {n for n in open_names if set(CACHE.get(n, [])) <= adm}


full = ENV | bridge
base = statable(full)
print(f"\nOPEN pooled propositions {len(open_names)}; statable {len(base)}")
print(f"  positive control -- statable under env alone: {len(statable(ENV))} "
      f"(must be < {len(base)}, else the bridge does nothing)")
for k in ("elided", "unrendered"):
    lost = sorted(base - statable(full - tiers[k]))
    print(f"\n  admitted ONLY via a {k!r} constant: {len(lost)}")
    for n in lost:
        print(f"     {n}  via {sorted(set(CACHE[n]) & tiers[k])}")
cons = statable(full - tiers["elided"] - tiers["unrendered"])
print(f"\nCONSERVATIVE statable (elided and unrendered both refused): "
      f"{len(cons)} of {len(open_names)}  [headline {len(base)}]")
