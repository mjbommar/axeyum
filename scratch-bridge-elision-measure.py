#!/usr/bin/env python3
"""Blast radius of bridge promotion by elision. Measurement only, not a gate."""
import json, pathlib, re, collections

ROOT = pathlib.Path(__file__).resolve().parent
A = ROOT / "artifacts" / "autogenesis"
CAT = json.loads((A / "mathlib-nat-int-fact-catalog-v1.json").read_text())
CACHE = json.loads((A / "mathlib-statement-constants-v1.json").read_text())["constants"]
ENV = set(json.loads((A / "kernel-environment-snapshot-v1.json").read_text())["declarations"])
VOC = json.loads((A / "mathlib-statable-vocabulary-v1.json").read_text())
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
print(f"catalogued={len(catalog)} settled={len(settled)} open={len(catalog)-len(settled)}")

missing_ks = [n for n in settled
              if not facts[settled[n]].get("formal", {}).get("kernel_statement")]
print(f"settled mirrors WITHOUT formal.kernel_statement: {len(missing_ks)}")
if missing_ks:
    print("  e.g.", missing_ks[:8])

TOK = re.compile(r"[A-Za-z_][A-Za-z0-9_.']*")


def logical(tok: str) -> str:
    head, _, rest = tok.partition(".")
    if head.startswith("Ax") and len(head) > 2 and head[2].isupper():
        head = head[2:]
    return head + ("." + rest if rest else "")


def kernel_tokens(stmt: str) -> set:
    out = set()
    for t in TOK.findall(stmt or ""):
        lg = logical(t)
        out.add(lg)
        out.add(lg.rsplit(".", 1)[-1])
    return out


ktoks = {n: kernel_tokens(facts[settled[n]].get("formal", {}).get("kernel_statement", ""))
         for n in settled}


def expressed_by(const, name):
    t = ktoks[name]
    return const in t or const.rsplit(".", 1)[-1] in t


bridge = set(VOC["bridge"])
witness = collections.defaultdict(list)
for n in settled:
    for c in CACHE.get(n, []):
        if c in bridge:
            witness[c].append(n)

elided, expressed = [], []
for c in sorted(bridge):
    ws = witness[c]
    hit = [n for n in ws if expressed_by(c, n)]
    (expressed if hit else elided).append((c, len(ws), len(hit)))

print(f"\nBRIDGE {len(bridge)}: expressed-by-some-witness={len(expressed)} "
      f"elided-by-all={len(elided)}")
print("\n-- ELIDED (no witnessing mirror's kernel type mentions it) --")
for c, w, h in elided:
    print(f"  {c:34s} witnesses={w}")
print("\n-- EXPRESSED (positive control; must be non-empty) --")
for c, w, h in expressed:
    print(f"  {c:34s} witnesses={w} expressing={h}")

elided_set = {c for c, _, _ in elided}
admissible_now = ENV | bridge
admissible_strict = ENV | (bridge - elided_set)
open_names = [n for n in catalog if n not in settled]
stat_now = [n for n in open_names if set(CACHE.get(n, [])) <= admissible_now]
stat_strict = [n for n in open_names if set(CACHE.get(n, [])) <= admissible_strict]
print(f"\nOPEN pooled propositions: {len(open_names)}")
print(f"  statable under current bridge : {len(stat_now)}")
print(f"  statable if elided dropped    : {len(stat_strict)}")
lost = sorted(set(stat_now) - set(stat_strict))
print(f"  admitted ONLY via an elided constant: {len(lost)}")
for n in lost:
    bad = sorted(set(CACHE.get(n, [])) & elided_set)
    print(f"    {n}  via {bad}")
