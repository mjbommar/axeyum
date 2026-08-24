#!/usr/bin/env python3
"""Validate accounting and safety boundaries of producer outcome observations."""
from __future__ import annotations
import json,pathlib,sys
from collections import Counter
from typing import Any
ROOT=pathlib.Path(__file__).resolve().parents[1]
PATH=ROOT/'artifacts/autogenesis/producer-outcome-observations-v1.json'
def validate(data:dict[str,Any])->list[str]:
 errors=[]
 if data.get('kind')!='axeyum-autogenesis-producer-outcome-observations':return ['invalid projection kind']
 if data.get('schema_version')!=1:errors.append('invalid schema version')
 derivation=data.get('derivation')
 if not isinstance(derivation,dict) or derivation.get('partitions')!=['development','train'] or not isinstance(derivation.get('trust_boundary'),str) or 'never held-out' not in derivation['trust_boundary']:errors.append('missing train/development-only trust boundary')
 for k in ('producer_census_manifest_sha256','reviewed_fact_catalog_sha256','observation_file_sha256','observation_sha256','mapping_sha256'):
  if not isinstance(derivation,dict) or not isinstance(derivation.get(k),str) or len(derivation[k])!=64:errors.append(f'missing digest: {k}')
 groups=data.get('groups')
 if not isinstance(groups,list):return errors+['groups must be a list']
 facts=[];keys=[];outcomes=Counter();classes=Counter();partitions=Counter()
 for g in groups:
  if not isinstance(g,dict):errors.append('group is not an object');continue
  key=tuple(g.get(k) for k in ('partition','family','statement_shape','abstraction_class','outcome'));keys.append(key)
  if not all(isinstance(v,str) and v for v in key):errors.append('group has invalid identity');continue
  if key[0] not in {'train','development'}:errors.append(f'{key}: group is outside train/development')
  if key[3] not in {'exact-source','semantic-abstraction'}:errors.append(f'{key}: invalid abstraction class')
  ids=g.get('observed_fact_ids')
  if not isinstance(ids,list) or ids!=sorted(set(ids)) or not all(isinstance(i,str) and i.startswith('F:') for i in ids):errors.append(f'{key}: facts must be sorted unique fact ids');continue
  if g.get('observed_fact_count')!=len(ids):errors.append(f'{key}: observed count disagrees with ids')
  facts.extend(ids);outcomes[key[4]]+=len(ids);classes[key[3]]+=len(ids);partitions[key[0]]+=len(ids)
 if keys!=sorted(set(keys)):errors.append('groups are not uniquely sorted')
 if len(facts)!=len(set(facts)):errors.append('fact occurs in more than one outcome group')
 census=data.get('census',{})
 if census.get('observed_facts')!=len(facts):errors.append('observed fact census disagrees with groups')
 if census.get('held_out_observed_facts')!=0:errors.append('held-out observations are forbidden')
 if census.get('partitions')!=dict(sorted(partitions.items())):errors.append('partition census disagrees with groups')
 if census.get('outcomes')!=dict(sorted(outcomes.items())):errors.append('outcome census disagrees with groups')
 if census.get('exact_source_facts')!=classes['exact-source'] or census.get('semantic_abstraction_facts')!=classes['semantic-abstraction']:errors.append('abstraction census disagrees with groups')
 if census.get('groups')!=len(groups):errors.append('group census disagrees with groups')
 return errors
def main():
 try:data=json.loads(PATH.read_text())
 except (OSError,json.JSONDecodeError) as e:print(f'AUTOGENESIS_PRODUCER_OUTCOMES_ERROR|cannot read projection: {e}',file=sys.stderr);return 1
 errors=validate(data)
 for e in errors:print(f'AUTOGENESIS_PRODUCER_OUTCOMES_ERROR|{e}',file=sys.stderr)
 if errors:return 1
 print(f"AUTOGENESIS_PRODUCER_OUTCOMES_OK|facts={data['census']['observed_facts']}|held_out={data['census']['held_out_observed_facts']}|groups={data['census']['groups']}");return 0
if __name__=='__main__':raise SystemExit(main())
