#!/usr/bin/env python3
"""Fail closed if the bounded Nat.ModEq capability target is no longer current."""
from __future__ import annotations
import json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1];P=ROOT/'artifacts/autogenesis/nat-modeq-capability-selection-v1.json';FACTS=ROOT/'artifacts/facts';OPS=ROOT/'artifacts/autogenesis/operations.json'
SELECTED=['F:ml430-nat-modeq-refl-d870c8f5','F:ml430-nat-modeq-symm-0a3d4d18','F:ml430-nat-modeq-trans-ef9d1c46'];DEFERRED='F:ml430-nat-modeq-comm-24b71e7a'
def fact(fid):return json.loads((FACTS/(fid.replace('F:','F-')+'.json')).read_text())
def validate(d):
 errors=[]
 if d.get('kind')!='axeyum-autogenesis-capability-candidate-selection':return ['invalid selection kind']
 if d.get('state')!='eligible-for-capability-construction-not-an-operation-registration':errors.append('selection state grants too much authority')
 if d.get('selected_facts')!=SELECTED:errors.append('selected fact order or identity changed')
 if 'cannot dispatch' not in d.get('trust_boundary',''):errors.append('selection lacks authority boundary')
 for fid in SELECTED:
  f=fact(fid)
  if f.get('epistemic_status')!='open' or f.get('depends_on')!=[] or f.get('formal',{}).get('fragment')!='Nat':errors.append(f'{fid}: no longer an open dependency-ready Nat target')
 deferred=fact(DEFERRED)
 if deferred.get('depends_on')!=[SELECTED[1]]:errors.append('deferred commutativity dependency changed')
 ops=json.loads(OPS.read_text())['operations']
 if any(fid in o.get('applicability',{}).get('fact_ids',[]) for o in ops for fid in SELECTED):errors.append('a selected fact is already operation-covered; selection is stale')
 return errors
def main():
 try:d=json.loads(P.read_text());errors=validate(d)
 except (OSError,json.JSONDecodeError,KeyError) as e:errors=[str(e)]
 for e in errors:print('AUTOGENESIS_NAT_MODEQ_SELECTION_ERROR|'+e,file=sys.stderr)
 if errors:return 1
 print('AUTOGENESIS_NAT_MODEQ_SELECTION_OK|selected=3|deferred=1|registered_operations=0');return 0
if __name__=='__main__':raise SystemExit(main())
