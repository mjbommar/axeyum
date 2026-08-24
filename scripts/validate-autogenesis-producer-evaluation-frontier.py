#!/usr/bin/env python3
"""Validate the partition-safe producer evaluation frontier."""
from __future__ import annotations
import json,pathlib,sys
from collections import Counter
ROOT=pathlib.Path(__file__).resolve().parents[1];P=ROOT/'artifacts/autogenesis/producer-evaluation-frontier-v1.json'
def validate(d):
 e=[]
 if d.get('kind')!='axeyum-autogenesis-producer-evaluation-frontier':return ['invalid frontier kind']
 if d.get('schema_version')!=1:e.append('invalid schema version')
 der=d.get('derivation',{})
 if not isinstance(der,dict) or der.get('evaluation_partitions')!=['development','train'] or 'never held-out' not in der.get('trust_boundary',''):e.append('missing held-out isolation boundary')
 groups=d.get('groups');
 if not isinstance(groups,list):return e+['groups must be a list']
 ids=[];keys=[];part=Counter()
 for g in groups:
  if not isinstance(g,dict):e.append('group is not an object');continue
  key=tuple(g.get(k) for k in ('partition','family','statement_shape','dependency_component_id'));keys.append(key)
  if not all(isinstance(x,str) and x for x in key):e.append('invalid group identity');continue
  if key[0] not in {'train','development'}:e.append(f'{key}: group outside evaluation partitions')
  fs=g.get('fact_ids')
  if not isinstance(fs,list) or fs!=sorted(set(fs)) or not all(isinstance(f,str) and f.startswith('F:') for f in fs):e.append(f'{key}: fact ids must be sorted and unique');continue
  if g.get('fact_count')!=len(fs):e.append(f'{key}: fact count disagrees with ids')
  ids.extend(fs);part[key[0]]+=len(fs)
 if keys!=sorted(set(keys)):e.append('groups are not uniquely sorted')
 if len(ids)!=len(set(ids)):e.append('fact appears in more than one group')
 c=d.get('census',{})
 if c.get('evaluation_dependency_ready_facts')!=len(ids):e.append('evaluation ready census disagrees with groups')
 if c.get('by_partition')!=dict(sorted(part.items())):e.append('partition census disagrees with groups')
 if c.get('groups')!=len(groups):e.append('group census disagrees with groups')
 for k in ('global_dependency_ready_facts','excluded_held_out_ready_facts','excluded_outside_evaluation_ready_facts'):
  if not isinstance(c.get(k),int) or c[k]<0:e.append(f'invalid census field: {k}')
 if c.get('global_dependency_ready_facts')!=len(ids)+c.get('excluded_held_out_ready_facts',0)+c.get('excluded_outside_evaluation_ready_facts',0):e.append('global ready census does not partition selection')
 controls=d.get('must_decline_control_fact_ids')
 if not isinstance(controls,list) or controls!=sorted(set(controls)) or not controls:e.append('must-decline controls must be nonempty sorted unique ids')
 elif not set(controls).issubset(ids):e.append('must-decline control is outside evaluation frontier')
 if c.get('must_decline_controls')!=(len(controls) if isinstance(controls,list) else None):e.append('must-decline control census disagrees with ids')
 if c.get('candidate_facts')!=len(ids)-(len(controls) if isinstance(controls,list) else 0):e.append('candidate census disagrees with control set')
 return e
def main():
 try:d=json.loads(P.read_text())
 except (OSError,json.JSONDecodeError) as x:print(f'AUTOGENESIS_EVALUATION_FRONTIER_ERROR|cannot read frontier: {x}',file=sys.stderr);return 1
 e=validate(d)
 for x in e:print('AUTOGENESIS_EVALUATION_FRONTIER_ERROR|'+x,file=sys.stderr)
 if e:return 1
 c=d['census'];print(f"AUTOGENESIS_EVALUATION_FRONTIER_OK|ready={c['evaluation_dependency_ready_facts']}|train={c['by_partition']['train']}|development={c['by_partition']['development']}|groups={c['groups']}");return 0
if __name__=='__main__':raise SystemExit(main())
