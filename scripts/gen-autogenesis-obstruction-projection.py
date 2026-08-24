#!/usr/bin/env python3
"""Normalize retained Autogenesis decline records into non-authoritative blockers."""
from __future__ import annotations
import argparse, json, pathlib, re, sys
from collections import defaultdict

ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCE = ROOT / "artifacts/autogenesis"
OUTPUT = SOURCE / "obstruction-projection-v1.json"
OVERLAY = SOURCE / "knowledge-overlay-v1.json"

def canonical(value: object) -> str:
    raw = str(value or "unclassified")
    return re.sub(r"[^a-z0-9]+", "-", raw.lower()).strip("-")

def family(name: str) -> str:
    return re.sub(r"-result-v\d+\.json$", "", name)

def candidate(category: str) -> str | None:
    if category in {"missingdeclaration", "unsupportedmissingdeclaration", "declarationabsent", "missingtargetowneddefinition"}:
        return "K:declaration-or-inductive-import"
    if category in {"typeshapemismatch", "typemismatch", "universearitymismatch", "decisionwitnessdependenttypeshape"}:
        return "K:typed-transport-composition"
    if category in {"resource-limit", "notfound", "leanpackageroot", "leanmodulesearchpath", "exportermodulesearchpath"}:
        return "K:bounded-reproducible-export"
    if category == "noadditions": return "K:checked-declaration-reuse"
    return None

def build() -> dict:
    try:
        overlay = json.loads(OVERLAY.read_text())
        registered_capabilities = {
            row["id"] for row in overlay.get("entities", [])
            if isinstance(row, dict) and row.get("kind") == "capability"
        }
    except (OSError, json.JSONDecodeError) as error:
        raise RuntimeError(f"cannot read knowledge overlay: {error}") from error
    episodes=[]
    for path in sorted(SOURCE.glob("*.json")):
        try: doc=json.loads(path.read_text())
        except json.JSONDecodeError: continue
        decline=doc.get("decline") if isinstance(doc,dict) else None
        if not isinstance(decline,dict): continue
        category=canonical(decline.get("class"))
        episodes.append({"id":f"E:{path.stem}","family":family(path.name),"source_artifact":str(path.relative_to(ROOT)),"goal":decline.get("name") or decline.get("operation") or doc.get("target") or doc.get("kind"),"adapter_outcome":"not-recorded","producer_outcome":"declined","reconstruction_outcome":"not-reached","checker_outcome":"not-reached","first_stage":decline.get("stage") or "not-recorded","observed_class":decline.get("class") or "unclassified","obstruction_category":category,"partial_kernel_published":bool(decline.get("partial_kernel_published",False))})
    groups=defaultdict(list)
    for e in episodes: groups[e["family"]].append(e)
    obstructions=[]
    for name, rows in sorted(groups.items()):
        categories=sorted({r["obstruction_category"] for r in rows})
        first=rows[0]
        proposed=candidate(first["obstruction_category"])
        status="not-applicable" if proposed is None else ("present-in-knowledge-overlay" if proposed in registered_capabilities else "not-present-in-knowledge-overlay")
        obstructions.append({"id":f"O:{name}","family":name,"first_observed_blocker":first["obstruction_category"],"complete_known_blocker_set":categories,"affected_episodes":[r["id"] for r in rows],"affected_population":{"episodes":len(rows),"facts":[]},"candidate_capability":proposed,"candidate_capability_internal_status":status,"resolution_commit":None,"measured_before_after":None})
    return {"schema_version":1,"kind":"axeyum-autogenesis-obstruction-projection","derivation":{"method":"mechanically-observed","scope":"retained top-level decline objects under artifacts/autogenesis","knowledge_overlay_path":"artifacts/autogenesis/knowledge-overlay-v1.json","trust_boundary":"obstructions rank investigation only; they never authorize proof admission"},"census":{"episodes":len(episodes),"obstructions":len(obstructions),"candidate_capability_statuses":{status:sum(o['candidate_capability_internal_status']==status for o in obstructions) for status in sorted({o['candidate_capability_internal_status'] for o in obstructions})}},"episodes":episodes,"obstructions":obstructions}

def main()->int:
    check=argparse.ArgumentParser(); check.add_argument('--check',action='store_true'); args=check.parse_args()
    rendered=json.dumps(build(),indent=2,sort_keys=True)+'\n'
    if args.check:
        if not OUTPUT.is_file() or OUTPUT.read_text()!=rendered:
            print('AUTOGENESIS_OBSTRUCTION_ERROR|projection is stale',file=sys.stderr); return 1
    else: OUTPUT.write_text(rendered)
    data=json.loads(rendered); print(f"AUTOGENESIS_OBSTRUCTION|episodes={data['census']['episodes']}|obstructions={data['census']['obstructions']}"); return 0
if __name__=='__main__': raise SystemExit(main())
