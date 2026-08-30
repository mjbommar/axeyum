#!/usr/bin/env python3
"""What our-side authority do the settled ml430 mirrors actually carry?"""
import json, pathlib, collections

ROOT = pathlib.Path(__file__).resolve().parent
A = ROOT / "artifacts" / "autogenesis"
CAT = json.loads((A / "mathlib-nat-int-fact-catalog-v1.json").read_text())
SETTLED = {"proved", "refuted", "computed"}

facts = {}
for p in sorted((ROOT / "artifacts" / "facts").glob("*.json")):
    f = json.loads(p.read_text())
    if isinstance(f.get("id"), str):
        facts[f["id"]] = f

catalog = {r["source_name"]: r["fact_id"] for r in CAT["facts"]
           if isinstance(r, dict) and r.get("kind") == "external-source"}
settled = {n: i for n, i in catalog.items()
           if facts.get(i, {}).get("epistemic_status") in SETTLED}

have_ks = have_kt = have_kd = neither = 0
kd_names = {}
for n, i in settled.items():
    f = facts[i]
    form = f.get("formal", {})
    ks = bool(form.get("kernel_statement"))
    kt = form.get("kernel_theorem")
    kds = [e.get("kernel_declaration") for e in f.get("evidence", [])
           if isinstance(e, dict) and e.get("kernel_declaration")]
    have_ks += ks
    have_kt += bool(kt)
    have_kd += bool(kds)
    if not ks and not kt and not kds:
        neither += 1
    name = kt or (kds[0] if kds else None)
    if name:
        kd_names[n] = name

print(f"settled={len(settled)}")
print(f"  formal.kernel_statement : {have_ks}")
print(f"  formal.kernel_theorem   : {have_kt}")
print(f"  evidence.kernel_declaration : {have_kd}")
print(f"  NONE of the three       : {neither}")
print(f"  resolvable to a kernel declaration NAME: {len(kd_names)}")

# do the resolvable names look like the mirror's own name?
same = sum(1 for n, k in kd_names.items() if k == n)
print(f"  of those, kernel name == mathlib source_name: {same}")
diff = [(n, k) for n, k in kd_names.items() if k != n]
print(f"  differing (first 10): {diff[:10]}")

missing = sorted(n for n in settled if n not in kd_names)
print(f"\nno kernel name at all ({len(missing)}):")
for n in missing[:20]:
    f = facts[settled[n]]
    print(f"   {n:44s} route={f.get('proof_route')} status={f.get('epistemic_status')}")
