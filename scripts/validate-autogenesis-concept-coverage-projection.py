#!/usr/bin/env python3
"""Validate the family-topic concept projection.

ADR-0553: the formalization and kernel-anchor dimensions are gone, and with them
the check that compared this file's anchors against the overlay's `formalizes`
links. That check had become `set() != set()` -- it could not fail. What remains
is checked against the crosswalk and the catalog, both of which are local.
"""
from __future__ import annotations
import json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1];P=ROOT/'artifacts/autogenesis/concept-coverage-projection-v1.json'
DEAD=('qualified_formalization_fact_ids','qualified_formalization_fact_count','qualified_formalization_statuses','formalization_qualifiers','kernel_semantic_anchor_ids','kernel_semantic_anchor_count')
def validate(d):
 errors=[]
 if d.get('kind')!='axeyum-autogenesis-concept-coverage-projection':return ['invalid projection kind']
 derivation=d.get('derivation',{})
 if not isinstance(derivation,dict) or derivation.get('evaluation_partitions')!=['development','train'] or 'never held-out' not in derivation.get('trust_boundary',''):errors.append('missing held-out isolation boundary')
 crosswalk=json.loads((ROOT/'artifacts/autogenesis/family-concept-crosswalk-v1.json').read_text())
 mapped={row['concept_id'] for row in crosswalk['mappings']}
 rows=d.get('concepts',[]);seen=set();topic=0;topic_facts=0
 for r in rows:
  ident=r.get('concept_id')
  if not isinstance(ident,str) or ident in seen:errors.append('concept ids must be unique strings')
  seen.add(ident)
  for key in DEAD:
   if key in r:errors.append(f'{ident}: {key} was removed by ADR-0553 and may not return without a local concept vocabulary')
  t=r.get('family_topic_fact_ids')
  if not isinstance(t,list) or t!=sorted(set(t)):errors.append(f'{ident}: family-topic facts must be sorted and unique');continue
  if r.get('family_topic_fact_count')!=len(t):errors.append(f'{ident}: family-topic count disagrees')
  if r.get('coverage_state')!='family-topic-only':errors.append(f'{ident}: the only coverage state is family-topic-only')
  topic+=bool(t);topic_facts+=len(t)
 if seen!=mapped:errors.append(f'projected concepts do not match the reviewed crosswalk ({sorted(seen-mapped)} extra, {sorted(mapped-seen)} missing)')
 census=d.get('census',{})
 if (census.get('concepts'),census.get('with_family_topic'),census.get('family_topic_facts'))!=(len(rows),topic,topic_facts):errors.append('coverage census disagrees with concepts')
 if not isinstance(census.get('excluded_held_out_family_topic_facts'),int) or census['excluded_held_out_family_topic_facts'] < 0:errors.append('invalid excluded held-out count')
 return errors
def main():
 d=json.loads(P.read_text());errors=validate(d)
 for e in errors:print('AUTOGENESIS_CONCEPT_COVERAGE_ERROR|'+e,file=sys.stderr)
 if errors:return 1
 print(f"AUTOGENESIS_CONCEPT_COVERAGE_OK|concepts={d['census']['concepts']}|topic_facts={d['census']['family_topic_facts']}");return 0
if __name__=='__main__':raise SystemExit(main())
