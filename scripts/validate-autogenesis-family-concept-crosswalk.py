#!/usr/bin/env python3
"""Validate the reviewed family-topic bridge without upgrading it to theorem meaning.

The `C:` ids are UNRESOLVED CITATION LABELS. Until 2026-08-24 this validator
required the crosswalk to pin a sibling repository's commit (`PIN`), which made
a topic label into a dependency; ADR-0553 removed the pin and this check with
it. Nothing here resolves a `C:` id, and `scripts/check-external-coupling.py`
refuses to let the path or the revision come back.
"""
from __future__ import annotations
import json,pathlib,re,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]
PATH=ROOT/'artifacts/autogenesis/family-concept-crosswalk-v1.json'
CATALOG=ROOT/'artifacts/autogenesis/mathlib-nat-int-fact-catalog-v1.json'
def validate(data):
 errors=[]
 if data.get('kind')!='axeyum-autogenesis-family-concept-crosswalk':return ['invalid crosswalk kind']
 if data.get('schema_version')!=1:errors.append('invalid schema version')
 if 'not fact formalization' not in data.get('trust_boundary',''):errors.append('trust boundary must deny fact formalization')
 try: catalog=json.loads(CATALOG.read_text());families={r['family'] for r in catalog['facts']}
 except (OSError,json.JSONDecodeError,KeyError) as e:return errors+[f'cannot read fact catalog: {e}']
 source=data.get('sources',{}); fact_source=source.get('fact_catalog',{})
 if fact_source.get('catalog_sha256')!=catalog.get('catalog_sha256'):errors.append('fact catalog digest differs')
 if 'math_education' in source:errors.append('crosswalk may not name an external source (ADR-0553)')
 if not data.get('topic_vocabulary'):errors.append('topic_vocabulary note is required: the C: ids are citations, not resolvable refs')
 rows=data.get('mappings',[]); seen=set()
 for row in rows:
  family=row.get('family');concept=row.get('concept_id')
  if family in seen:errors.append(f'duplicate family {family}')
  seen.add(family)
  if family not in families:errors.append(f'unknown catalog family {family}')
  if not isinstance(concept,str) or not re.fullmatch(r'C:[a-z0-9]+(?:-[a-z0-9]+)*',concept):errors.append(f'invalid concept id {concept}')
  if row.get('assurance')!='human-reviewed' or not row.get('reason'):errors.append(f'{family}: mapping lacks reviewed rationale')
 if seen!=families:errors.append('mappings do not cover exactly the catalog families')
 return errors
def main():
 try:data=json.loads(PATH.read_text())
 except (OSError,json.JSONDecodeError) as e:print(f'AUTOGENESIS_FAMILY_CONCEPT_ERROR|{e}',file=sys.stderr);return 1
 errors=validate(data)
 for e in errors:print(f'AUTOGENESIS_FAMILY_CONCEPT_ERROR|{e}',file=sys.stderr)
 if errors:return 1
 print(f"AUTOGENESIS_FAMILY_CONCEPT_OK|families={len(data['mappings'])}|external_sources=0");return 0
if __name__=='__main__':raise SystemExit(main())
