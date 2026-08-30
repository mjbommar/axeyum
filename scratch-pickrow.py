import json, pathlib
A = pathlib.Path(__file__).resolve().parent / "artifacts" / "autogenesis"
v = json.loads((A / "mathlib-statable-vocabulary-v1.json").read_text())
bridge = set(v["bridge"])
rows = v["settled"]
allc = {c for r in rows for c in r["constants"]}
for r in rows:
    if set(r["constants"]) & bridge:
        continue
    rest = {c for o in rows if o is not r for c in o["constants"]}
    print(r["source_name"], "distinct_stable=", rest == allc)
