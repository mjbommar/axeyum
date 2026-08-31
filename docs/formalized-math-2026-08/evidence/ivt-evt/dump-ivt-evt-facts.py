import json, glob, os

pats = ["F-creal-ivt-*.json", "F-creal-evt-*.json", "F-creal-crossing*.json",
        "F-cas-ivt-*.json", "F-cas-evt-*.json", "F-cas-extremum-*.json",
        "F-cas-mvt-*.json"]
base = "artifacts/facts"
files = []
for p in pats:
    files += sorted(glob.glob(os.path.join(base, p)))
print("FILES:", len(files))
for f in files:
    d = json.load(open(f))
    fo = d.get("formal", {}) or {}
    prov = d.get("provenance", {}) or {}
    ev = d.get("evidence", []) or []
    print("=" * 78)
    print("ID:", d.get("id"))
    print("  epistemic:", d.get("epistemic_status"), "| external:", d.get("external_status"))
    print("  curation:", prov.get("curation"), "| producer:", prov.get("producer"))
    print("  axioms:", d.get("axiom_footprint"))
    print("  formal.kind:", fo.get("kind"), "| lang:", fo.get("language"),
          "| name:", fo.get("declaration") or fo.get("name"))
    st = fo.get("statement") or ""
    print("  TYPE:", st.replace("\n", " ")[:1500])
    for e in ev:
        print("  EV kind=%s checked=%s" % (e.get("kind"), e.get("checked")))
        cc = e.get("checker_command")
        if cc:
            print("     cmd:", str(cc)[:400])
        de = e.get("description") or e.get("summary")
        if de:
            print("     desc:", str(de)[:300])
