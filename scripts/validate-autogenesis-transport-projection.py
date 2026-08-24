#!/usr/bin/env python3
from __future__ import annotations
import json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1];P=ROOT/'artifacts/autogenesis/transport-projection-v1.json'
ALLOWED_BINDINGS={'statement-and-goal','adapter-goal-and-target'}
def validate(d):
 bad=[]; ids=set(); complete=0
 if d.get('kind')!='axeyum-autogenesis-transport-projection': return ['invalid projection kind']
 for c in d.get('chains',[]):
  ident=c.get('id')
  if not isinstance(ident,str) or ident in ids: bad.append('chain ids must be unique strings')
  ids.add(ident)
  evidence=c.get('checked_evidence_ids'); bindings=c.get('checked_evidence_bindings'); status=c.get('status')
  if status=='complete':
   complete+=1
   if not evidence or not c.get('source_statement_sha256') or not c.get('imported_goal_sha256'):bad.append(f'{ident}: complete chain lacks identity or evidence')
   if not isinstance(bindings,list) or not bindings:bad.append(f'{ident}: complete chain lacks evidence binding')
   else:
    binding_ids=[row.get('evidence_id') for row in bindings if isinstance(row,dict)]
    if sorted(binding_ids)!=sorted(evidence):bad.append(f'{ident}: evidence ids and bindings disagree')
    for row in bindings:
     if not isinstance(row,dict) or row.get('binding') not in ALLOWED_BINDINGS:bad.append(f'{ident}: unknown evidence binding')
     elif row['binding']=='adapter-goal-and-target' and not c.get('target_content_sha256'):bad.append(f'{ident}: adapter binding lacks target-content hash')
  elif status=='incomplete-no-matching-fact-evidence':
   if evidence or bindings:bad.append(f'{ident}: incomplete chain carries evidence')
  else: bad.append(f'{ident}: unknown status')
 if d.get('census',{}).get('chains')!=len(d.get('chains',[])) or d.get('census',{}).get('complete')!=complete:bad.append('transport census disagrees with chains')
 return bad
def main():
 d=json.loads(P.read_text()); bad=validate(d)
 if bad:print('AUTOGENESIS_TRANSPORT_ERROR|'+','.join(bad),file=sys.stderr);return 1
 print(f"AUTOGENESIS_TRANSPORT_OK|chains={len(d['chains'])}|complete={d['census']['complete']}");return 0
if __name__=='__main__':raise SystemExit(main())
