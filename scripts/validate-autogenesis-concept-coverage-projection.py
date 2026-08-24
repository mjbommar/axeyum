#!/usr/bin/env python3
from __future__ import annotations
import json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1];P=ROOT/'artifacts/autogenesis/concept-coverage-projection-v1.json'
def validate(d):
 errors=[]
 if d.get('kind')!='axeyum-autogenesis-concept-coverage-projection':return ['invalid projection kind']
 rows=d.get('concepts',[]);seen=set();topic=formal=0;topic_facts=formal_facts=0
 for r in rows:
  ident=r.get('concept_id')
  if not isinstance(ident,str) or ident in seen:errors.append('concept ids must be unique strings')
  seen.add(ident);t=r.get('family_topic_fact_ids');f=r.get('qualified_formalization_fact_ids')
  if not isinstance(t,list) or t!=sorted(set(t)):errors.append(f'{ident}: family-topic facts must be sorted and unique');continue
  if not isinstance(f,list) or f!=sorted(set(f)):errors.append(f'{ident}: formalization facts must be sorted and unique');continue
  if r.get('family_topic_fact_count')!=len(t):errors.append(f'{ident}: family-topic count disagrees')
  if r.get('qualified_formalization_fact_count')!=len(f):errors.append(f'{ident}: formalization count disagrees')
  expected='fact-formalization-present' if f else 'family-topic-only'
  if r.get('coverage_state')!=expected:errors.append(f'{ident}: coverage state conflates dimensions')
  topic+=bool(t);formal+=bool(f);topic_facts+=len(t);formal_facts+=len(f)
 census=d.get('census',{})
 if (census.get('concepts'),census.get('with_family_topic'),census.get('with_fact_formalization'),census.get('family_topic_facts'),census.get('qualified_formalization_facts'))!=(len(rows),topic,formal,topic_facts,formal_facts):errors.append('coverage census disagrees with concepts')
 return errors
def main():
 d=json.loads(P.read_text());errors=validate(d)
 for e in errors:print('AUTOGENESIS_CONCEPT_COVERAGE_ERROR|'+e,file=sys.stderr)
 if errors:return 1
 print(f"AUTOGENESIS_CONCEPT_COVERAGE_OK|concepts={d['census']['concepts']}|formal={d['census']['with_fact_formalization']}|topic_facts={d['census']['family_topic_facts']}");return 0
if __name__=='__main__':raise SystemExit(main())
