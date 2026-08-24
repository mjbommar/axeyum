#!/usr/bin/env python3
"""Derive separated family-topic and fact-formalization concept coverage."""
from __future__ import annotations
import argparse,hashlib,json,pathlib,sys
from collections import Counter,defaultdict
ROOT=pathlib.Path(__file__).resolve().parents[1]
AUTO=ROOT/'artifacts/autogenesis'; FACTS=ROOT/'artifacts/facts'; OUT=AUTO/'concept-coverage-projection-v1.json'
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def build():
 catalog_path=AUTO/'mathlib-nat-int-fact-catalog-v1.json';crosswalk_path=AUTO/'family-concept-crosswalk-v1.json';overlay_path=AUTO/'knowledge-overlay-v1.json';nursery_path=AUTO/'nursery-v1.json'
 catalog=json.loads(catalog_path.read_text());crosswalk=json.loads(crosswalk_path.read_text());overlay=json.loads(overlay_path.read_text());nursery=json.loads(nursery_path.read_text())
 facts={json.loads(p.read_text())['id']:json.loads(p.read_text()) for p in FACTS.glob('*.json')}
 partition={row['fact_id']:row['partition'] for row in nursery['entries']};visible={'train','development'}
 families=defaultdict(list)
 for row in catalog['facts']:families[row['family']].append(row['fact_id'])
 topic=defaultdict(list)
 for row in crosswalk['mappings']:topic[row['concept_id']].extend(f for f in families[row['family']] if partition.get(f) in visible)
 formal=defaultdict(list); qualifiers=defaultdict(Counter)
 for link in overlay['links']:
  if link['relation']=='formalizes' and partition.get(link['source']['id']) in visible:
   concept=link['target']['id']; formal[concept].append(link['source']['id']); qualifiers[concept][link['qualifiers']['coverage']]+=1
 rows=[]
 for concept in sorted(set(topic)|set(formal)):
  topic_ids=sorted(set(topic[concept]));formal_ids=sorted(set(formal[concept]))
  statuses=Counter(facts[f]['epistemic_status'] for f in formal_ids if f in facts)
  rows.append({'concept_id':concept,'family_topic_fact_ids':topic_ids,'family_topic_fact_count':len(topic_ids),'qualified_formalization_fact_ids':formal_ids,'qualified_formalization_fact_count':len(formal_ids),'qualified_formalization_statuses':dict(sorted(statuses.items())),'formalization_qualifiers':[{'coverage':k,'fact_count':qualifiers[concept][k]} for k in sorted(qualifiers[concept])],'coverage_state':'fact-formalization-present' if formal_ids else 'family-topic-only','trust':'family-topic and fact-formalization dimensions remain separate'})
 return {'schema_version':1,'kind':'axeyum-autogenesis-concept-coverage-projection','derivation':{'catalog_sha256':sha(catalog_path),'crosswalk_sha256':sha(crosswalk_path),'overlay_sha256':sha(overlay_path),'nursery_sha256':sha(nursery_path),'evaluation_partitions':['development','train'],'trust_boundary':'train/development coverage reporting only; never held-out inspection, proof, operation, or admission authority'},'census':{'concepts':len(rows),'with_family_topic':sum(bool(r['family_topic_fact_ids']) for r in rows),'with_fact_formalization':sum(bool(r['qualified_formalization_fact_ids']) for r in rows),'family_topic_facts':sum(r['family_topic_fact_count'] for r in rows),'qualified_formalization_facts':sum(r['qualified_formalization_fact_count'] for r in rows),'excluded_held_out_family_topic_facts':sum(1 for r in catalog['facts'] if partition.get(r['fact_id'])=='held-out')},'concepts':rows}
def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();rendered=json.dumps(build(),indent=2,sort_keys=True)+'\n'
 if a.check:
  if not OUT.is_file() or OUT.read_text()!=rendered:print('AUTOGENESIS_CONCEPT_COVERAGE_ERROR|projection is stale',file=sys.stderr);return 1
 else:OUT.write_text(rendered)
 d=json.loads(rendered);print(f"AUTOGENESIS_CONCEPT_COVERAGE|concepts={d['census']['concepts']}|formal={d['census']['with_fact_formalization']}|topic_facts={d['census']['family_topic_facts']}");return 0
if __name__=='__main__':raise SystemExit(main())
