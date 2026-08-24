#!/usr/bin/env python3
"""Derive hash-bound source/adapter/goal/evidence chains; never join by name."""
from __future__ import annotations
import argparse,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; AUTO=ROOT/'artifacts/autogenesis'; FACTS=ROOT/'artifacts/facts'; OUT=AUTO/'transport-projection-v1.json'
def build():
  facts={json.loads(p.read_text())['id']:(p,json.loads(p.read_text())) for p in FACTS.glob('*.json')}
  chains=[]
  for p in sorted(AUTO.glob('*.json')):
    try:d=json.loads(p.read_text())
    except:continue
    if d.get('kind')!='axeyum-autogenesis-mathlib-statement-adapter':continue
    fid=d.get('source_fact_id'); fact=facts.get(fid); goal=d.get('independent_import',{}).get('goal_sha256'); statement=d.get('source_statement_sha256')
    evidence=[]
    if fact:
      for e in fact[1].get('evidence',[]):
        op=e.get('checker_operation',{})
        if op.get('formal_statement_sha256')==statement and op.get('goal_sha256')==goal: evidence.append(e.get('id'))
    chains.append({'id':'T:'+p.stem,'source_fact_id':fid,'adapter_manifest':str(p.relative_to(ROOT)),'source_statement_sha256':statement,'adapter_ndjson_sha256':d.get('external_artifact',{}).get('sha256'),'imported_goal_sha256':goal,'target_content_sha256':d.get('independent_import',{}).get('target_content_sha256'),'checked_evidence_ids':sorted(evidence),'status':'complete' if evidence else 'incomplete-no-matching-fact-evidence','trust':'identity-bound-sidecar-not-admission-authority'})
  return {'schema_version':1,'kind':'axeyum-autogenesis-transport-projection','derivation':{'method':'checker-derived','join_policy':'fact id plus exact statement and goal sha256; no declaration-name fallback'},'census':{'chains':len(chains),'complete':sum(c['status']=='complete' for c in chains)},'chains':chains}
def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();r=json.dumps(build(),indent=2,sort_keys=True)+'\n'
 if a.check:
  if not OUT.is_file() or OUT.read_text()!=r:print('AUTOGENESIS_TRANSPORT_ERROR|stale',file=sys.stderr);return 1
 else:OUT.write_text(r)
 d=json.loads(r);print(f"AUTOGENESIS_TRANSPORT|chains={d['census']['chains']}|complete={d['census']['complete']}");return 0
if __name__=='__main__':raise SystemExit(main())
