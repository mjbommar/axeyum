import importlib.util, json, pathlib, sys, collections
ROOT = pathlib.Path(".").resolve()
spec = importlib.util.spec_from_file_location("refill", ROOT/"scripts/gen-autogenesis-nursery-refill.py")
R = importlib.util.module_from_spec(spec); spec.loader.exec_module(R)

snapshot = R.load_json(R.ENV_SNAPSHOT)
env = set(snapshot["declarations"])
inventory = R.read_inventory()
catalog = R.load_json(R.CATALOG)
registry = R.load_json(R.REGISTRY)["constructions"]
facts = {}
for p in sorted(R.FACTS.glob("*.json")):
    f = json.loads(p.read_text()); facts[f["id"]] = f
vocab = R.read_vocabulary(env, inventory, catalog, facts)
adm = R.admissible(env, vocab)
catalogued = {r["source_name"] for r in catalog["facts"] if r["kind"]=="external-source"}

drawn_modules = {m for ms in R.FAMILY_MODULES.values() for m in ms}
print(f"INVENTORY|records={len(inventory)}|env={len(env)}|adm={len(adm)}|catalogued={len(catalogued)}|families_drawn={len(R.FAMILY_MODULES)}|modules_drawn={len(drawn_modules)}")

per_module = collections.defaultdict(list)
reasons = collections.Counter()
for name in sorted(inventory):
    rec = inventory[name]
    mod = rec["module"]
    if name in catalogued:
        reasons["already-catalogued"] += 1; continue
    if R.HYGIENE.search(name):
        reasons["hygienic-or-generated"] += 1; continue
    consts = set(R.CONST_RE.findall(rec["type_repr"]))
    if consts - adm:
        reasons["not-statable-here"] += 1; continue
    if consts & R.HELD_OUT_CONSTRUCTIONS:
        reasons["held-out-construction"] += 1; continue
    if R.blockers_for(rec["type"], registry):
        reasons["divergence-registry"] += 1; continue
    reasons["screened-ok"] += 1
    per_module[mod].append(name)

print("REASONS|" + "|".join(f"{k}={v}" for k,v in sorted(reasons.items())))
total_ok = sum(len(v) for v in per_module.values())
undrawn_mods = {m:v for m,v in per_module.items() if m not in drawn_modules}
drawn_mods_residual = {m:v for m,v in per_module.items() if m in drawn_modules}
print(f"SCREENED_OK|total={total_ok}|modules={len(per_module)}")
print(f"UNDRAWN_MODULES|modules={len(undrawn_mods)}|rows={sum(len(v) for v in undrawn_mods.values())}")
print(f"DRAWN_MODULE_RESIDUAL|modules={len(drawn_mods_residual)}|rows={sum(len(v) for v in drawn_mods_residual.values())}")
solo = {m:v for m,v in undrawn_mods.items() if len(v)>=R.PER_FAMILY}
print(f"UNDRAWN_MODULES_ANCHOR_ALONE(>={R.PER_FAMILY})|modules={len(solo)}|rows={sum(len(v) for v in solo.values())}")
for m,v in sorted(undrawn_mods.items(), key=lambda kv:-len(kv[1]))[:80]:
    print(f"  MOD|{len(v):4d}|{m}")
json.dump({m:v for m,v in sorted(per_module.items())}, open(".lane-scratch/refill-economics/per-module.json","w"), indent=1)
