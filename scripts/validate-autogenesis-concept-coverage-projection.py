#!/usr/bin/env python3
from __future__ import annotations
import json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1];P=ROOT/'artifacts/autogenesis/concept-coverage-projection-v1.json'
def validate(d):
 errors=[]
 if d.get('kind')!='axeyum-autogenesis-concept-coverage-projection':return ['invalid projection kind']
 derivation=d.get('derivation',{})
 if not isinstance(derivation,dict) or derivation.get('evaluation_partitions')!=['development','train'] or 'never held-out' not in derivation.get('trust_boundary',''):errors.append('missing held-out isolation boundary')
 rows=d.get('concepts',[]);seen=set();topic=formal=kernel=0;topic_facts=formal_facts=kernel_anchors=0
 for r in rows:
  ident=r.get('concept_id')
  if not isinstance(ident,str) or ident in seen:errors.append('concept ids must be unique strings')
  seen.add(ident);t=r.get('family_topic_fact_ids');f=r.get('qualified_formalization_fact_ids')
  if not isinstance(t,list) or t!=sorted(set(t)):errors.append(f'{ident}: family-topic facts must be sorted and unique');continue
  if not isinstance(f,list) or f!=sorted(set(f)):errors.append(f'{ident}: formalization facts must be sorted and unique');continue
  k=r.get('kernel_semantic_anchor_ids')
  if not isinstance(k,list) or k!=sorted(set(k)):errors.append(f'{ident}: kernel anchors must be sorted and unique');continue
  if r.get('family_topic_fact_count')!=len(t):errors.append(f'{ident}: family-topic count disagrees')
  if r.get('qualified_formalization_fact_count')!=len(f):errors.append(f'{ident}: formalization count disagrees')
  if r.get('kernel_semantic_anchor_count')!=len(k):errors.append(f'{ident}: kernel anchor count disagrees')
  expected='fact-formalization-present' if f else ('kernel-semantic-anchor-present' if k else 'family-topic-only')
  if r.get('coverage_state')!=expected:errors.append(f'{ident}: coverage state conflates dimensions')
  topic+=bool(t);formal+=bool(f);kernel+=bool(k);topic_facts+=len(t);formal_facts+=len(f);kernel_anchors+=len(k)
 census=d.get('census',{})
 if (census.get('concepts'),census.get('with_family_topic'),census.get('with_fact_formalization'),census.get('with_kernel_semantic_anchor'),census.get('family_topic_facts'),census.get('qualified_formalization_facts'),census.get('kernel_semantic_anchors'))!=(len(rows),topic,formal,kernel,topic_facts,formal_facts,kernel_anchors):errors.append('coverage census disagrees with concepts')
 if not isinstance(census.get('excluded_held_out_family_topic_facts'),int) or census['excluded_held_out_family_topic_facts'] < 0:errors.append('invalid excluded held-out count')
 overlay=json.loads((ROOT/'artifacts/autogenesis/knowledge-overlay-v1.json').read_text())
 expected={(link['target']['id'],link['source']['id']) for link in overlay['links'] if link['relation']=='formalizes' and link['status']=='active' and link['source']['namespace']=='axeyum-kernel' and link['source']['kind']=='kernel-declaration'}
 actual={(r['concept_id'],anchor) for r in rows for anchor in r.get('kernel_semantic_anchor_ids',[])}
 if actual!=expected:errors.append('kernel semantic anchors do not exactly match active overlay links')
 return errors
def main():
 d=json.loads(P.read_text());errors=validate(d)
 for e in errors:print('AUTOGENESIS_CONCEPT_COVERAGE_ERROR|'+e,file=sys.stderr)
 if errors:return 1
 print(f"AUTOGENESIS_CONCEPT_COVERAGE_OK|concepts={d['census']['concepts']}|formal={d['census']['with_fact_formalization']}|topic_facts={d['census']['family_topic_facts']}");return 0
if __name__=='__main__':raise SystemExit(main())
