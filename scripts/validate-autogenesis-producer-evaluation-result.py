#!/usr/bin/env python3
"""Fail-closed validator for a future general-producer result artifact."""
from __future__ import annotations
import argparse,hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1];PROTO=ROOT/'artifacts/autogenesis/producer-evaluation-protocol-v1.json';FRONTIER=ROOT/'artifacts/autogenesis/producer-evaluation-frontier-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def validate(d):
 e=[];p=json.loads(PROTO.read_text());f=json.loads(FRONTIER.read_text());ids={x for g in f['groups'] for x in g['fact_ids']};controls=set(f['must_decline_control_fact_ids'])
 if d.get('kind')!='axeyum-autogenesis-producer-evaluation-result' or d.get('schema_version')!=1:e.append('invalid result identity')
 if d.get('protocol_sha256')!=sha(PROTO):e.append('result is not bound to current protocol')
 rows=d.get('rows');seen=set()
 if not isinstance(rows,list):return e+['rows must be a list']
 for r in rows:
  if not isinstance(r,dict) or set(r)!={'fact_id','adapter','producer','reconstruction','checker'}:e.append('row has invalid shape');continue
  i=r['fact_id'];seen.add(i)
  if i not in ids:e.append(f'row outside evaluation frontier: {i}')
  if i in controls and any(r[x] in {'kernel-accepted','cleanly-reproduced','admitted'} for x in ('producer','reconstruction','checker')):e.append(f'must-decline control was accepted: {i}')
 if seen!=ids:e.append('result does not account for every evaluation fact exactly once')
 if len(seen)!=len(rows):e.append('result duplicates a fact')
 fn=d.get('funnel',{})
 if not isinstance(fn,dict) or list(fn)!=['eligible','proposals','kernel_accepted','cleanly_reproduced','admitted']:e.append('invalid funnel shape')
 elif fn['eligible']!=len(ids) or not all(isinstance(fn[x],int) and 0<=fn[x]<=len(ids) for x in fn) or not (fn['admitted']<=fn['cleanly_reproduced']<=fn['kernel_accepted']<=fn['proposals']<=fn['eligible']):e.append('funnel is not monotone or does not cover frontier')
 return e
def main():
 a=argparse.ArgumentParser();a.add_argument('result',type=pathlib.Path);x=a.parse_args()
 try:d=json.loads(x.result.read_text());e=validate(d)
 except (OSError,json.JSONDecodeError,KeyError) as z:print(f'AUTOGENESIS_EVALUATION_RESULT_ERROR|{z}',file=sys.stderr);return 1
 for z in e:print('AUTOGENESIS_EVALUATION_RESULT_ERROR|'+z,file=sys.stderr)
 if e:return 1
 print(f"AUTOGENESIS_EVALUATION_RESULT_OK|eligible={d['funnel']['eligible']}|admitted={d['funnel']['admitted']}");return 0
if __name__=='__main__':raise SystemExit(main())
