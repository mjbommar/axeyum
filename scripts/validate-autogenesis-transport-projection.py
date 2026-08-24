#!/usr/bin/env python3
from __future__ import annotations
import json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1];P=ROOT/'artifacts/autogenesis/transport-projection-v1.json'
def main():
 d=json.loads(P.read_text()); bad=[]
 for c in d.get('chains',[]):
  if c['status']=='complete' and (not c['checked_evidence_ids'] or not c['source_statement_sha256'] or not c['imported_goal_sha256']):bad.append(c['id'])
  if c['status']!='complete' and c['checked_evidence_ids']:bad.append(c['id'])
 if bad:print('AUTOGENESIS_TRANSPORT_ERROR|invalid chains='+','.join(bad),file=sys.stderr);return 1
 print(f"AUTOGENESIS_TRANSPORT_OK|chains={len(d['chains'])}|complete={d['census']['complete']}");return 0
if __name__=='__main__':raise SystemExit(main())
