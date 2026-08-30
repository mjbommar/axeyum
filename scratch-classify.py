#!/usr/bin/env python3
"""Partition the bridge: elaboration vs vocabulary, then test vocabulary."""
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


def is_elaboration(c: str) -> bool:
    head, _, last = c.rpartition(".")
    last = last or c
    if re.match(r"^inst[A-Z]", last):
        return True
    if head and last == head.rpartition(".")[2][:1].lower() + head.rpartition(".")[2][1:]:
        return True
    return False


TOK = re.compile(r"[A-Za-z_][A-Za-z0-9_.']*")


def logical(t):
    h, _, r = t.partition(".")
    if h.startswith("Ax") and len(h) > 2 and h[2].isupper():
        h = h[2:]
    return h + ("." + r if r else "")


def ktoks(stmt):
    out = set()
    for t in TOK.findall(stmt or ""):
        lg = logical(t)
        out.add(lg)
        out.add(lg.rsplit(".", 1)[-1])
    return out


rendering = {n: facts[settled[n]].get("formal", {}).get("kernel_statement")
             for n in settled}
toks = {n: ktoks(r) for n, r in rendering.items() if r}

bridge = sorted(VOC["bridge"])
witness = collections.defaultdict(list)
for n in settled:
    for c in CACHE.get(n, []):
        if c in bridge:
            witness[c].append(n)

cls = {}
for c in bridge:
    if is_elaboration(c):
        cls[c] = "elaboration"
        continue
    ws = witness[c]
    rendered = [n for n in ws if n in toks]
    if not rendered:
        cls[c] = "unrendered"
    elif any(c in toks[n] or c.rsplit(".", 1)[-1] in toks[n] for n in rendered):
        cls[c] = "expressed"
    else:
        cls[c] = "elided"

counts = collections.Counter(cls.values())
print("bridge partition:", dict(sorted(counts.items())), "total", sum(counts.values()))
for k in ("elaboration", "expressed", "elided", "unrendered"):
    names = [c for c in bridge if cls[c] == k]
    print(f"\n{k} ({len(names)}):")
    for c in names:
        ws = witness[c]
        r = [n for n in ws if n in toks]
        print(f"   {c:32s} witnesses={len(ws):3d} rendered={len(r):3d}")
