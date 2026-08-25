#!/usr/bin/env python3
"""Derive family-topic concept coverage from the reviewed crosswalk.

ADR-0553 REMOVED TWO OF THE THREE DIMENSIONS, and the reason matters more than
the fields do. `qualified_formalization_*` and `kernel_semantic_anchor_*` were
both read from the knowledge overlay's `formalizes` links, whose targets lived
in a namespace resolved against a sibling repository. When those links went, the
two dimensions became STRUCTURALLY EMPTY -- not zero on this tree, but incapable
of a nonzero value -- and the validator's strongest check degenerated to
comparing two empty sets, which is a check that cannot fail.

Rather than ship three census columns pinned at zero and a vacuous guard, the
generator now emits only the dimension that still measures something: which
train/development facts sit in a catalog family the reviewed crosswalk maps to a
topic label. Restoring the other two is not a matter of re-adding fields; it
needs a concept vocabulary this repository owns and can adjudicate, which is
exactly the prerequisite ADR-0553 records.
"""
from __future__ import annotations
import argparse,hashlib,json,pathlib,sys
from collections import defaultdict
ROOT=pathlib.Path(__file__).resolve().parents[1]
AUTO=ROOT/'artifacts/autogenesis'; OUT=AUTO/'concept-coverage-projection-v1.json'
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def build():
 catalog_path=AUTO/'mathlib-nat-int-fact-catalog-v1.json';crosswalk_path=AUTO/'family-concept-crosswalk-v1.json';nursery_path=AUTO/'nursery-v1.json'
 catalog=json.loads(catalog_path.read_text());crosswalk=json.loads(crosswalk_path.read_text());nursery=json.loads(nursery_path.read_text())
 partition={row['fact_id']:row['partition'] for row in nursery['entries']};visible={'train','development'}
 families=defaultdict(list)
 for row in catalog['facts']:families[row['family']].append(row['fact_id'])
 topic=defaultdict(list)
 for row in crosswalk['mappings']:topic[row['concept_id']].extend(f for f in families[row['family']] if partition.get(f) in visible)
 rows=[]
 for concept in sorted(topic):
  topic_ids=sorted(set(topic[concept]))
  rows.append({'concept_id':concept,'family_topic_fact_ids':topic_ids,'family_topic_fact_count':len(topic_ids),'coverage_state':'family-topic-only','trust':'family-topic guidance only; the C: id is an unresolved citation label, not a formalization target'})
 return {'schema_version':1,'kind':'axeyum-autogenesis-concept-coverage-projection','derivation':{'catalog_sha256':sha(catalog_path),'crosswalk_sha256':sha(crosswalk_path),'nursery_sha256':sha(nursery_path),'evaluation_partitions':['development','train'],'trust_boundary':'train/development family-topic coverage only; never held-out inspection, proof, operation, or admission authority','removed_dimensions':'ADR-0553 removed qualified_formalization_* and kernel_semantic_anchor_*; both were read from overlay formalizes links resolved against an external repository, and both became structurally empty when it was removed'},'census':{'concepts':len(rows),'with_family_topic':sum(bool(r['family_topic_fact_ids']) for r in rows),'family_topic_facts':sum(r['family_topic_fact_count'] for r in rows),'excluded_held_out_family_topic_facts':sum(1 for r in catalog['facts'] if partition.get(r['fact_id'])=='held-out')},'concepts':rows}
def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();rendered=json.dumps(build(),indent=2,sort_keys=True)+'\n'
 if a.check:
  if not OUT.is_file() or OUT.read_text()!=rendered:print('AUTOGENESIS_CONCEPT_COVERAGE_ERROR|projection is stale',file=sys.stderr);return 1
 else:OUT.write_text(rendered)
 d=json.loads(rendered);print(f"AUTOGENESIS_CONCEPT_COVERAGE|concepts={d['census']['concepts']}|topic_facts={d['census']['family_topic_facts']}");return 0
if __name__=='__main__':raise SystemExit(main())
