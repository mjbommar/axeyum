#!/usr/bin/env python3
"""Generate non-authoritative, measured producer observations for scheduling."""
from __future__ import annotations
import argparse,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; OUT=ROOT/'artifacts/autogenesis/scheduler-observations-v1.json'
def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
 ops=json.loads((ROOT/'artifacts/autogenesis/operations.json').read_text())['operations']; over=json.loads((ROOT/'artifacts/autogenesis/knowledge-overlay-v1.json').read_text()); trans=json.loads((ROOT/'artifacts/autogenesis/transport-projection-v1.json').read_text())
 credited={l['source']['id']:l['target']['id'] for l in over['links'] if l['relation']=='established-by'}; mapped={l['source']['id'] for l in over['links'] if l['relation']=='formalizes'}; complete={c['source_fact_id'] for c in trans['chains'] if c['status']=='complete'}
 rows=[]
 for o in ops:
  fs=o['applicability']['fact_ids']
  if o['scope']!='authoritative' or len(fs)<2:continue
  rows.append({'operation_id':o['id'],'applicable_facts':len(fs),'evidence_credited_facts':sum(credited.get(f)==o['id'] for f in fs),'qualified_formal_mappings':sum(f in mapped for f in fs),'complete_transport_chains':sum(f in complete for f in fs),'observation_kind':'mechanically-observed','admission_authority':False})
 d={'schema_version':1,'kind':'axeyum-autogenesis-scheduler-observations','trust_boundary':'ranking input only; never proof/admission authority','observations':rows}
 r=json.dumps(d,indent=2,sort_keys=True)+'\n'
 if a.check:
  if not OUT.is_file() or OUT.read_text()!=r:print('AUTOGENESIS_SCHEDULER_ERROR|stale',file=sys.stderr);return 1
 else:OUT.write_text(r)
 print(f"AUTOGENESIS_SCHEDULER|operations={len(rows)}");return 0
if __name__=='__main__':raise SystemExit(main())
